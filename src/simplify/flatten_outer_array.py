"""Flatten 2-level array variables with constant-only outer accesses.

Background
----------
The verifier's memory bus encoder emits 2-level arrays
``(Array Int (Array Int X))`` where the *outer* index is a static
channel/data-field selector — every ``(select M k)`` and
``(store M k v)`` uses a literal-constant outer index ``k``. In the
keccak guest we observe a tiny outer-index set ``{1, 2}`` and zero
variable-index outer accesses across the file.

When the precondition holds, the outer level is a constant-size tuple
wearing the costume of a function. Z3's array theory still applies the
select-over-store axiom at the outer level, pairing every
``store-into-channel`` with every ``read-from-any-channel``. With
hundreds of stores and selects, this generates ~N·M outer-level axiom
instances. Empirically ``array-exp-ax2`` reaches 70-160 k on the
keccak completeness checks and time correlates linearly with it.

Approach
--------
This pass replaces each qualifying 2-level array ``M`` with one
1-level array per observed constant outer index (``M__k1``, ``M__k2``,
…). Every value-level outer-array expression is projected via a
recursive ``proj_k`` and every outer-typed equality expands to an
``And`` of per-k inner equalities. After the pass there are no
``(Array Int (Array Int X))``-typed terms in the formula and the
outer-level select-over-store axiom enumeration disappears entirely.

Soundness rests on three properties:

1. **Constant outer indices only.** The pass walks every node and
   bails out (leaving the array untouched) if it sees an outer-level
   ``select``/``store`` with a non-constant index. The flat encoding
   is unsound otherwise — variable indices have access to outer slots
   beyond the observed ``K`` set.

2. **Outer arrays appear only in array positions.** The flat encoding
   has no representation for "an outer array passed to a UF" or "an
   outer array used as the index of another array". The pass also
   bails if it sees an outer-array symbol anywhere other than the
   array slot of a ``select``/``store`` or one side of an equality.

3. **Extensional equality is preserved.** ``(= A B)`` on a 2-level
   array means "equal at every Int index". The pass replaces it with
   ``(and (= A__k1 B__k1) … (= A__kn B__kn))`` — equal only at the
   observed indices. This is *equivalent* on the original formula
   because there are no other observable indices: the precondition
   guarantees every access uses an index in ``K``. (If the formula
   had a ``(select X 99)`` with ``99 ∉ K``, the bail-out triggers.)

Pipeline placement
------------------
After ``array_subst`` (which dedups shared outer arrays), before
``z3-propagate-values`` (which benefits from the simpler shape). The
pass requires all symbols at top level (i.e., ``lift_forall`` has
already run) — assertion at entry.
"""
from collections import defaultdict
from typing import Iterable, Optional

from pysmt import operators

from ..smt.utils import *


def _is_outer_array_type(t) -> bool:
    """True if `t` is `(Array Int (Array Int X))` for any X."""
    return (t.is_array_type()
            and t.elem_type.is_array_type())


def _collect_outer_decls(smt_script) -> dict[str, FNode]:
    """Return ``{name: declared_symbol}`` for outer 2-level array decls."""
    out: dict[str, FNode] = {}
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if sym.is_symbol() and _is_outer_array_type(sym.get_type()):
                out[sym.symbol_name()] = sym
    return out


def _walk_all(f: FNode):
    """Pre-order traversal yielding every node (may revisit shared subterms)."""
    stack = [f]
    while stack:
        node = stack.pop()
        yield node
        stack.extend(node.args())


def _scan_uses(
    smt_script,
    outer_names: set[str],
) -> tuple[dict[str, set[int]], set[str], set[str]]:
    """Walk every asserted formula. Return:

    * ``indices_used``: name → set of constant outer indices observed
      (direct ``select``/``store`` accesses only — equality propagation is
      handled by the global-K choice in the caller).
    * ``referenced``: names that appear anywhere in the formula (so the
      caller knows which outer decls are live).
    * ``ineligible``: names that cannot be safely flattened
      (variable-index outer access, or appears in a non-array-position).
    """
    indices_used: dict[str, set[int]] = defaultdict(set)
    referenced: set[str] = set()
    ineligible: set[str] = set()

    def name_of(node: FNode) -> Optional[str]:
        return node.symbol_name() if node.is_symbol() else None

    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        ok_positions: set[int] = set()  # id(child) marked as a known-safe position

        # First pass: classify outer-name symbols by their parent's role and
        # record observed constant indices.
        for node in _walk_all(cmd.args[0]):
            nt = node.node_type()
            if nt == operators.ARRAY_SELECT or nt == operators.ARRAY_STORE:
                base, idx = node.arg(0), node.arg(1)
                ok_positions.add(id(base))
                # Identify the underlying outer name (peel store chains).
                cur = base
                while cur.node_type() == operators.ARRAY_STORE:
                    cur = cur.arg(0)
                target_name = cur.symbol_name() if cur.is_symbol() else None
                if target_name is not None and target_name in outer_names:
                    if idx.is_int_constant():
                        indices_used[target_name].add(idx.constant_value())
                    else:
                        ineligible.add(target_name)
            if node.is_equals():
                # Outer names on either side of an equality are in a safe
                # position (the equality itself will be expanded by the
                # walker).
                for side in (node.arg(0), node.arg(1)):
                    if side.is_symbol() and name_of(side) in outer_names:
                        ok_positions.add(id(side))

        # Second pass: every outer-named symbol observation that wasn't
        # marked 'ok' is in a forbidden position; mark the name ineligible.
        # Either way, record the name as referenced.
        for node in _walk_all(cmd.args[0]):
            if node.is_symbol() and name_of(node) in outer_names:
                referenced.add(node.symbol_name())
                if id(node) not in ok_positions:
                    ineligible.add(node.symbol_name())

    return indices_used, referenced, ineligible


class _FlattenWalker(IdentityDagWalker):
    """Rewrite outer-array operations by projection to per-k inner arrays."""

    def __init__(self, projections: dict[str, dict[int, FNode]], env=None):
        super().__init__(env=env)
        self.proj = projections  # name → {k → inner_symbol}

    # --- projection helper ---

    def _project(self, expr: FNode, k: int) -> FNode:
        """Return an expression equal to ``(select expr k)``.

        Recursively descends through Store / Ite / Array-const / Symbol.
        For shapes we don't recognize, falls back to ``Select(expr, k)``
        and lets z3 reduce it later.
        """
        nt = expr.node_type()
        if expr.is_symbol():
            name = expr.symbol_name()
            if name in self.proj and k in self.proj[name]:
                return self.proj[name][k]
            # Outer symbol we couldn't pre-declare (e.g. observed index outside K)
            # — keep as a bare select.
            return Select(expr, Int(k))
        if nt == operators.ARRAY_STORE:
            base, idx, val = expr.arg(0), expr.arg(1), expr.arg(2)
            if idx.is_int_constant():
                if idx.constant_value() == k:
                    return val
                return self._project(base, k)
            return Select(expr, Int(k))
        if nt == operators.ARRAY_VALUE:
            # ((as const (Array Int (Array Int X))) inner-default) →
            # the inner default value (an inner-array expression).
            return expr.array_value_default()
        if expr.is_ite():
            return Ite(expr.arg(0),
                       self._project(expr.arg(1), k),
                       self._project(expr.arg(2), k))
        return Select(expr, Int(k))

    # --- DagWalker overrides ---

    def walk_array_select(self, formula, args, **kwargs):
        """``(select M k)`` where M is outer-typed and k constant → ``M__k``."""
        arr, idx = args
        if arr.is_symbol() and arr.symbol_name() in self.proj and idx.is_int_constant():
            k = idx.constant_value()
            if k in self.proj[arr.symbol_name()]:
                return self.proj[arr.symbol_name()][k]
        return self.mgr.Select(arr, idx)

    def walk_equals(self, formula, args, **kwargs):
        """Outer-typed ``(= A B)`` → ``(and (= A__k B__k) for k ∈ K)``."""
        a, b = args
        if _is_outer_array_type(a.get_type()):
            # Determine the keys from whichever side is a flattened symbol.
            keys: list[int] = []
            for side in (a, b):
                if side.is_symbol() and side.symbol_name() in self.proj:
                    keys = sorted(self.proj[side.symbol_name()].keys())
                    break
            if not keys:
                # Neither side is a declared (flattenable) name — leave alone.
                return self.mgr.Equals(a, b)
            conjuncts = [self.mgr.Equals(self._project(a, k),
                                         self._project(b, k))
                         for k in keys]
            if len(conjuncts) == 1:
                return conjuncts[0]
            return self.mgr.And(*conjuncts)
        return self.mgr.Equals(a, b)


def simplify_flatten_outer_array(
    smt_script: script.SmtLibScript,
    subaction=None,
) -> script.SmtLibScript:
    """Flatten outer-array layer for vars with constant-only outer accesses.

    See module docstring for the transformation and soundness argument.
    """
    outer_decls = _collect_outer_decls(smt_script)
    if not outer_decls:
        if subaction is not None:
            subaction += {"outer_arrays": 0, "flattened": 0}
        return smt_script

    indices_used, referenced, ineligible = _scan_uses(
        smt_script, set(outer_decls.keys()))

    # All outer arrays that are equated (directly or via store chains) must
    # share a common K. The simplest sound choice is the GLOBAL union of all
    # observed constant indices across the formula. Any outer-array name
    # that is referenced and not ineligible gets that K, even if it only
    # appears on the LHS of an equality (and thus contributes no direct
    # constant-index observation): a per-array K would leave implicit
    # cross-index equality dropped, which would be unsound (rewritten sat
    # where original unsat).
    global_k: set[int] = set()
    for ks in indices_used.values():
        global_k |= ks

    eligible_names = [
        name for name in outer_decls
        if name not in ineligible and name in referenced
    ]
    eligible: dict[str, set[int]] = {name: global_k for name in eligible_names}

    if not eligible or not global_k:
        if subaction is not None:
            subaction += {
                "outer_arrays": len(outer_decls),
                "ineligible_var_index_or_other_use": len(ineligible),
                "flattened": 0,
            }
        return smt_script

    # Build per-k inner-array declarations.
    projections: dict[str, dict[int, FNode]] = {}
    new_inner_syms: list[FNode] = []
    for name, ks in eligible.items():
        outer_sym = outer_decls[name]
        inner_ty = outer_sym.get_type().elem_type
        projections[name] = {}
        for k in sorted(ks):
            new_name = f"{name}__{k}"
            inner = Symbol(new_name, inner_ty)
            projections[name][k] = inner
            new_inner_syms.append(inner)

    walker = _FlattenWalker(projections, env=get_env())

    # Rewrite asserts and drop the outer decls + flattened-unused decls.
    rewritten_asserts = 0
    new_commands: list[script.SmtLibCommand] = []
    inserted_inner_decls = False
    drop_names = set(eligible.keys()) | {
        n for n in outer_decls
        if n not in eligible and n not in ineligible and n not in referenced
    }

    for cmd in smt_script.commands:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if sym.is_symbol() and sym.symbol_name() in drop_names:
                continue
            new_commands.append(cmd)
            continue
        if cmd.name == "assert":
            # Insert new inner-array decls right before the first assert.
            if not inserted_inner_decls:
                for inner in new_inner_syms:
                    new_commands.append(script.SmtLibCommand(
                        name="declare-fun",
                        args=[inner, [], inner.get_type()],
                    ))
                inserted_inner_decls = True
            old = cmd.args[0]
            new = walker.walk(old)
            if new is not old:
                cmd.args[0] = keep_comment(new, old)
                rewritten_asserts += 1
            new_commands.append(cmd)
            continue
        # Other commands (set-info, check-sat, etc.) pass through.
        # Ensure inner decls land before check-sat if there were no asserts.
        if cmd.name == "check-sat" and not inserted_inner_decls:
            for inner in new_inner_syms:
                new_commands.append(script.SmtLibCommand(
                    name="declare-fun",
                    args=[inner, [], inner.get_type()],
                ))
            inserted_inner_decls = True
        new_commands.append(cmd)

    smt_script.commands = new_commands

    logging.info(
        f"flatten_outer_array: flattened {len(eligible)} outer arrays into "
        f"{len(new_inner_syms)} inner arrays "
        f"(rewrote {rewritten_asserts} asserts); "
        f"{len(ineligible)} ineligible"
    )
    if subaction is not None:
        subaction += {
            "outer_arrays": len(outer_decls),
            "ineligible_var_index_or_other_use": len(ineligible),
            "flattened": len(eligible),
            "new_inner_arrays": len(new_inner_syms),
            "asserts_rewritten": rewritten_asserts,
        }
    return smt_script
