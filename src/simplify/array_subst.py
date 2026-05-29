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
   the base and final arrays equated by ``build_io_relation``),
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
SETINFO_CMD_PREFIX = ":shared-array-"


def _free_symbols_in_asserts(smt_script: script.SmtLibScript) -> set[FNode]:
    """Union of free variables appearing in every ``assert`` command."""
    out: set[FNode] = set()
    for cmd in smt_script.commands:
        if cmd.name == "assert":
            out |= cmd.args[0].get_free_variables()
    return out


class _ArraySubstWalker(IdentityDagWalker):
    """Replace array symbols; match by ``symbol_name`` to the canonical ``declare-fun`` node."""

    def __init__(self, subs: dict[FNode, FNode], all_declared: dict[str, FNode], *args, **kwargs):
        """``subs``: UF-style chain of array renames; ``all_declared``: name → canonical symbol."""
        super().__init__(*args, **kwargs)
        self.subs = subs
        self.all_declared = all_declared

    def walk_symbol(self, formula, args, **kwargs):
        """Follow ``subs`` to a representative, keyed by canonical ``declare-fun`` symbol."""
        canon = self.all_declared.get(formula.symbol_name(), formula)
        cur = canon
        while cur in self.subs:
            cur = self.subs[cur]
        return cur


def _extract_equalities(f: FNode):
    """Yield all equalities from a formula (bare or inside top-level And)."""
    if f.is_equals():
        yield f
    elif f.is_and():
        for conj in f.args():
            if conj.is_equals():
                yield conj


def simplify_array_subst(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Assert shared bus equalities and substitute away redundant array declarations.

    Two independent transformations run in sequence:

    1. **Syntactic substitution** of existing ``(assert (= A B))`` where
       both ``A`` and ``B`` are declared array symbols.  One symbol is
       globally replaced by the other, its ``declare-fun`` is dropped,
       and the equality assertion is removed.  A union-find keeps the
       mapping consistent when multiple equalities chain together.
       Symbols are matched by ``symbol_name`` to the canonical
       ``declare-fun`` node so every occurrence rewrites even when the
       parser produced duplicate ``Symbol`` objects for the same name.

    2. **Shared-array assertion injection**: equalities read from
       ``set-info :shared-array-N`` annotations are turned into
       ``(assert (= before-X after-X))`` commands inserted just before
       ``check-sat``.  A pin is emitted only when both sides are plain
       symbols whose names still have a ``declare-fun`` in the script
       (after phase~2), and each name occurs free in some existing
       ``assert`` (name-based, so parser/cache symbol identity cannot
       resurrect eliminated arrays).  Matching ``set-info`` rows are
       then removed from the script.
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
    # These are emitted by ``emit_memory_equalities`` in ``verify.memory_bus_alignment`` (array + plain).
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
    # These come from ``build_io_relation`` in the encoding
    # (the base/final arrays of each memory bus).  They are safe to
    # substitute syntactically because they are simple renamings with
    # no store chains attached.

    subs: dict[FNode, FNode] = {}
    drop_formulas: set[int] = set()

    def _resolve(sym: FNode) -> FNode:
        """Follow array rename map ``subs`` to a root representative."""
        while sym in subs:
            sym = subs[sym]
        return sym

    for cmd in smt_script.commands:
        if cmd.name != "assert":
            continue
        for eq in _extract_equalities(cmd.args[0]):
            a, b = eq.arg(0), eq.arg(1)
            if not (a.is_symbol() and b.is_symbol()):
                continue
            a = all_declared.get(a.symbol_name())
            b = all_declared.get(b.symbol_name())
            if a is None or b is None:
                continue
            if a not in array_declared or b not in array_declared:
                continue
            ra, rb = _resolve(a), _resolve(b)
            if ra != rb:
                subs[rb] = ra
                drop_formulas.add(id(eq))

    dead_syms: set[FNode] = set()
    if subs:
        for sym in list(subs.keys()):
            s = sym
            while s in subs:
                dead_syms.add(s)
                s = subs[s]

        walker = _ArraySubstWalker(subs, all_declared, env=get_env())

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

    referenced = _free_symbols_in_asserts(smt_script)
    referenced_names = {s.symbol_name() for s in referenced if s.is_symbol()}
    declared_by_name: dict[str, FNode] = {}
    for cmd in smt_script.commands:
        if cmd.name != "declare-fun":
            continue
        s = cmd.args[0]
        if s.is_symbol():
            declared_by_name[s.symbol_name()] = s

    # --- Phase 3: inject shared-array assertions ---
    # These are NOT substituted (see module docstring for rationale).
    # Instead they are emitted as ``(assert ...)`` just before
    # ``check-sat`` so Z3's congruence closure can propagate them
    # internally.

    shared_bus_asserts_injected = 0
    if pin_assertions:
        check_sat_idx = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )
        added = 0
        for eq in pin_assertions:
            a, b = _resolve(eq.arg(0)), _resolve(eq.arg(1))
            if a == b or not (a.is_symbol() and b.is_symbol()):
                continue
            an, bn = a.symbol_name(), b.symbol_name()
            if an not in referenced_names or bn not in referenced_names:
                continue
            a_c = declared_by_name.get(an)
            b_c = declared_by_name.get(bn)
            if a_c is None or b_c is None:
                continue
            cmd = script.SmtLibCommand(name="assert", args=[Equals(a_c, b_c)])
            smt_script.commands.insert(check_sat_idx, cmd)
            check_sat_idx += 1
            added += 1
        shared_bus_asserts_injected = added
        logging.info(f"array-subst: added {added} shared assertions")

    if dead_syms:
        logging.info(f"array-subst: eliminated {len(dead_syms)} array symbols")

    smt_script.commands = [
        cmd
        for cmd in smt_script.commands
        if not (
            cmd.name == "set-info"
            and len(cmd.args) >= 1
            and isinstance(cmd.args[0], str)
            and cmd.args[0].startswith(SETINFO_CMD_PREFIX)
        )
    ]

    if subaction is not None:
        subaction += {
            "setinfo_shared_array_pins": len(pins),
            "resolved_pin_equalities": len(pin_assertions),
            "array_rename_edges": len(subs),
            "shared_bus_asserts_injected": shared_bus_asserts_injected,
            "dead_array_symbols": len(dead_syms),
        }

    return smt_script
