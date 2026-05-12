"""Array simplifier pass: shared-bus assertions and redundant-equality substitution.

Background
----------
The memory bus is encoded as a chain of array variables (one per bus
interaction step), with ``Store``/``Select`` operations linking each
step to the next.  In the verification encoding, both the *before* and
*after* sides produce their own independent chain, even when many (or
all) bus interactions are identical between the two sides.  This means
Z3 must reason about extensional equality of hundreds of 2D array pairs,
which dominates solver time via ``array-ax2`` and ``array-exp-ax2``
lemma instantiation.

Approach
--------
This pass exploits two sources of information to reduce array-theory
overhead:

1. **Shared-array set-info pins** (``shared-array-N``):  The verifier
   encoding (``verifier.py``) compares the memory bus interaction lists
   of the two sides (modulo name prefix).  For every contiguous prefix
   and suffix of interactions that are structurally identical, the
   corresponding intermediate array symbols are provably equal.  These
   equalities are emitted as ``(set-info :shared-array-N ...)``
   annotations.

   This pass reads them and injects ``(assert (= before-X after-X))``
   for each such pair.  We do **not** substitute one for the other:
   Z3's internal congruence closure handles asserted equalities far
   more efficiently than our syntactic substitution (which would
   duplicate store chains on a single base array, increasing lemma
   instantiation).

2. **Existing top-level array equalities**: When the encoding already
   contains ``(assert (= A B))`` for two array-typed symbols (e.g.
   the base and final arrays equated by ``build_input_output_relation``),
   this pass *does* substitute ``B → A`` throughout and removes ``B``'s
   declaration and the equality assertion.  These are always present
   and safe to eliminate syntactically because they are bare equalities,
   not part of a store chain.

Pipeline placement
------------------
This pass runs immediately after ``lift`` (when the formula is
quantifier-free and all symbols are declared at top level), and before
``z3-propagate-values``.
"""

from ..smt.utils import *
from .skolem_utils import load_setinfo_pins

SETINFO_PREFIX = "shared-array-"


class _ArraySubstWalker(IdentityDagWalker):
    """Replace symbols according to a substitution map."""

    def __init__(self, subs: dict[FNode, FNode], *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.subs = subs

    def walk_symbol(self, formula, args, **kwargs):
        return self.subs.get(formula, formula)


def _extract_equalities(f: FNode):
    """Yield all equalities from a formula (bare or inside top-level And)."""
    if f.is_equals():
        yield f
    elif f.is_and():
        for conj in f.args():
            if conj.is_equals():
                yield conj


def simplify_array_subst(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Assert shared bus equalities and substitute away redundant array declarations.

    Two independent transformations run in sequence:

    1. **Syntactic substitution** of existing ``(assert (= A B))`` where
       both ``A`` and ``B`` are declared array symbols.  One symbol is
       globally replaced by the other, its ``declare-fun`` is dropped,
       and the equality assertion is removed.  A union-find keeps the
       mapping consistent when multiple equalities chain together.

    2. **Shared-array assertion injection**: equalities read from
       ``set-info :shared-array-N`` annotations are turned into
       ``(assert (= before-X after-X))`` commands inserted just before
       ``check-sat``.  Only equalities whose free variables are all
       declared in the current script are emitted (the ``lift`` pass
       may have dropped some symbols).
    """

    # --- Collect declarations ---

    all_declared: dict[str, FNode] = {}
    array_declared: set[FNode] = set()
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if sym.is_symbol():
                all_declared[sym.symbol_name()] = sym
                if sym.get_type().is_array_type():
                    array_declared.add(sym)

    # --- Phase 1: read shared-array pins ---
    # These are emitted by _shared_bus_arrays() in verifier.py.
    # The set-info value is a serialized ``(= before-X after-X)``
    # equation.  We resolve symbol names against the current script's
    # declarations to get the actual FNode objects (the parser may
    # have created fresh nodes during round-trip).

    pins = load_setinfo_pins(smt_script, SETINFO_PREFIX)
    pin_assertions: list[FNode] = []
    for eq in pins:
        if not eq.is_equals():
            continue
        a, b = eq.arg(0), eq.arg(1)
        a_sym = all_declared.get(a.symbol_name()) if a.is_symbol() else None
        b_sym = all_declared.get(b.symbol_name()) if b.is_symbol() else None
        if a_sym is not None and b_sym is not None:
            pin_assertions.append(Equals(a_sym, b_sym))

    # --- Phase 2: substitute existing array-array equalities ---
    # These come from ``build_input_output_relation`` in the encoding
    # (the base/final arrays of each memory bus).  They are safe to
    # substitute syntactically because they are simple renamings with
    # no store chains attached.

    subs: dict[FNode, FNode] = {}
    drop_formulas: set[int] = set()

    def _resolve(sym: FNode) -> FNode:
        while sym in subs:
            sym = subs[sym]
        return sym

    for cmd in smt_script.commands:
        if cmd.name != "assert":
            continue
        for eq in _extract_equalities(cmd.args[0]):
            a, b = eq.arg(0), eq.arg(1)
            if a in array_declared and b in array_declared:
                ra, rb = _resolve(a), _resolve(b)
                if ra != rb:
                    subs[rb] = ra
                    drop_formulas.add(id(eq))

    dead_syms = set()
    if subs:
        for sym in list(subs.keys()):
            s = sym
            while s in subs:
                dead_syms.add(s)
                s = subs[s]

        walker = _ArraySubstWalker(subs, env=get_env())

        def _rewrite_formula(f: FNode) -> FNode | None:
            """Apply the substitution to ``f``, dropping consumed equalities."""
            if id(f) in drop_formulas:
                return None
            if f.is_and():
                kept = []
                for conj in f.args():
                    if id(conj) not in drop_formulas:
                        kept.append(walker.walk(conj))
                if not kept:
                    return None
                if len(kept) == 1:
                    return kept[0]
                return And(*kept)
            return walker.walk(f)

        new_commands = []
        for cmd in smt_script.commands:
            if cmd.name == "declare-fun" and cmd.args[0] in dead_syms:
                continue
            if cmd.name == "assert":
                result = _rewrite_formula(cmd.args[0])
                if result is None:
                    continue
                cmd.args[0] = keep_comment(result, cmd.args[0])
            new_commands.append(cmd)
        smt_script.commands = new_commands

    # --- Phase 3: inject shared-array assertions ---
    # These are NOT substituted (see module docstring for rationale).
    # Instead they are emitted as ``(assert ...)`` just before
    # ``check-sat`` so Z3's congruence closure can propagate them
    # internally.

    if pin_assertions:
        all_declared_set = set(all_declared.values())
        check_sat_idx = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )
        added = 0
        for eq in pin_assertions:
            if eq.get_free_variables() <= all_declared_set:
                cmd = script.SmtLibCommand(name="assert", args=[eq])
                smt_script.commands.insert(check_sat_idx, cmd)
                check_sat_idx += 1
                added += 1
        logging.info(f"array-subst: added {added} shared assertions")

    if dead_syms:
        logging.info(f"array-subst: eliminated {len(dead_syms)} array symbols")

    return smt_script
