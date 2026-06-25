"""Flatten array variables with constant-only accesses (staged, deepest first).

Background
----------
The verifier's memory bus encoder emits 2-level arrays
``(Array Int (Array Int X))`` where both index levels are static
selectors — every ``(select M k)`` and ``(store M k v)`` uses a
literal-constant index. In the keccak guest:

* outer-level indices: ``{1, 2}``,
* inner-level indices: ``{2, 4, 8, 32}``,
* zero variable-index accesses at either level.

Z3's array theory applies the select-over-store axiom at every
nesting level, pairing every ``store-into-slot`` with every
``read-from-any-slot``. Empirically ``array-exp-ax2`` reaches
70-160k on these benchmarks and time correlates linearly with it.

Approach
--------
The pass eliminates one level of array nesting per round, **deepest
first**:

* Round 1 collects only the deepest-typed array decls (2-level if
  any are present). Each qualifying ``(Array Int (Array Int X))``
  ``M`` is split into one ``(Array Int X)`` decl per observed
  outer-index (``M__k1, …, M__kn``). Every value-level outer-array
  expression is projected via ``_project`` and every outer-typed
  equality expands to an ``And`` of per-k inner equalities.
* Round 2 sees no more 2-level arrays. The maximum depth is now 1,
  so it collects every ``(Array Int X)`` decl (including both the
  pre-existing inner arrays and the round-1 outputs) and splits each
  into scalars per observed inner-index. The variables created here
  are not arrays.

Each round's fresh variables are at a strictly *shallower* nesting
depth than the variables it processes — round 1 creates 1-level
arrays out of 2-level arrays, round 2 creates scalars out of 1-level
arrays. So no round needs to re-process its own outputs in the same
round; the fixpoint terminates after one round per nesting level
that the input formula has.

The walker is depth-agnostic: ``walk_equals`` checks "is this an
array equality?" and dispatches based on whether either side is in
the round's projections map. Round-staging is achieved purely via
``_collect_outer_decls``'s max-depth filter.

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
   guarantees every access uses an index in ``K``.

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
from ..utils.stats import stats_dump


def _is_outer_array_type(t) -> bool:
    """True if `t` is any array type. Depth-filtering happens at the
    declaration-collection level (``_collect_outer_decls``); the walker
    is depth-agnostic and only fires when one of the equality's operands
    is in the round's projections map."""
    return t.is_array_type()


def _array_depth(t) -> int:
    """0 for non-array, 1 for ``(Array Int X)`` with scalar X, 2 for
    ``(Array Int (Array Int X))``, etc."""
    d = 0
    while t.is_array_type():
        d += 1
        t = t.elem_type
    return d


def _collect_outer_decls(smt_script) -> dict[str, FNode]:
    """Return ``{name: declared_symbol}`` for arrays at the current
    maximum array-depth.

    The pass flattens one nesting level per round (deepest first). After
    round 1, the previously-outer 2-level arrays are gone and the
    previously-inner 1-level arrays are now at max depth — round 2
    picks them up. The freshly-created variables in each round have a
    type that's *strictly shallower* than the variables being flattened
    (one level deeper element type → one level shallower), so no
    round-N variable creation forces a same-round re-pass.
    """
    all_arr_decls: dict[str, FNode] = {}
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if sym.is_symbol() and sym.get_type().is_array_type():
                all_arr_decls[sym.symbol_name()] = sym
    if not all_arr_decls:
        return {}
    max_d = max(_array_depth(s.get_type()) for s in all_arr_decls.values())
    return {n: s for n, s in all_arr_decls.items()
            if _array_depth(s.get_type()) == max_d}


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


def _eq(mgr, a: FNode, b: FNode) -> FNode:
    """Equals for non-Bool, Iff for Bool. pysmt forbids Equals on Bool."""
    if a.get_type().is_bool_type():
        return mgr.Iff(a, b)
    return mgr.Equals(a, b)


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
        """Outer-typed ``(= A B)`` → ``(and (eq A__k B__k) for k ∈ K)``.

        ``eq`` is ``Iff`` when the projected element type is Bool, else
        ``Equals`` (pysmt forbids ``Equals`` on Booleans).
        """
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
            conjuncts = [
                _eq(self.mgr, self._project(a, k), self._project(b, k))
                for k in keys
            ]
            if len(conjuncts) == 1:
                return conjuncts[0]
            return self.mgr.And(*conjuncts)
        return self.mgr.Equals(a, b)


def simplify_flatten_outer_array(
    smt_script: script.SmtLibScript,
    subaction=None,
) -> script.SmtLibScript:
    """Repeatedly flatten array decls with constant-only accesses.

    Runs ``_flatten_one_round`` to a fixpoint (bounded iteration count
    so we don't loop forever on pathological inputs). Each round
    handles arrays whose accesses are all literal-constant indices;
    after flattening an outer ``(Array Int (Array Int X))`` into per-k
    ``(Array Int X)`` inner arrays, the next round may flatten the
    inner arrays into scalars (and so on).

    See module docstring for the per-round transformation and
    soundness argument.
    """
    total_flattened = 0
    total_new = 0
    total_rewrites = 0
    total_ineligible = 0
    rounds = 0
    # CURRENTLY CAPPED AT 1 (= flatten outer arrays only).
    #
    # The deepest-first staging in `_collect_outer_decls` correctly picks
    # the 2-level arrays in round 1, leaving 1-level inner arrays for
    # round 2 — and conceptually this should work without recursion
    # issues since round 1's outputs are 1-level (matching the inner
    # arrays in depth). Empirically, however, round 2 introduces a
    # spurious sat on apc_candidate_2099512_031_low_degree_bus-..._032
    # _inlining.completeness when combined with the loose skolem_names
    # pin: replay-validation (extracting the round-2 model's scalar
    # values for the 401 vars that exist in the pre-flatten formula and
    # asserting them there) returns UNSAT, so the round-2 model is not
    # a model of the pre-flatten formula — meaning round 2 introduced
    # an unsoundness in *something*. The bug is somewhere in how round 2
    # rewrites equalities involving the round-1 outputs (newly-declared
    # 1-level arrays) — likely walk_equals or _project missing a case.
    #
    # Until that's diagnosed, only run round 1 (outer-only flatten).
    # All the staging infrastructure stays in place for future work.
    MAX_ROUNDS = 1
    round_stats_list: list[dict] = []
    while rounds < MAX_ROUNDS:
        round_stats = _flatten_one_round(smt_script)
        if round_stats["flattened"] == 0:
            break
        rounds += 1
        stats_dump("flatten_outer_array-round", {"round": rounds, **round_stats})
        round_stats_list.append({"round": rounds, **round_stats})
        total_flattened += round_stats["flattened"]
        total_new += round_stats["new_inner_arrays"]
        total_rewrites += round_stats["asserts_rewritten"]
        total_ineligible = round_stats["ineligible"]
    logging.info(
        f"flatten_outer_array: total {total_flattened} arrays flattened into "
        f"{total_new} per-index decls across {rounds} round(s) "
        f"({total_rewrites} asserts rewritten; "
        f"{total_ineligible} ineligible at final round)"
    )
    stats_dump(
        "flatten_outer_array",
        {
            "rounds": rounds,
            "flattened_total": total_flattened,
            "new_inner_arrays_total": total_new,
            "asserts_rewritten_total": total_rewrites,
            "ineligible_at_final_round": total_ineligible,
            "rounds_detail": round_stats_list,
        },
    )

    # Contract: at the end of this pass, no 2D+ array declaration may
    # remain. Outer arrays are this pass's responsibility, and an
    # upstream pass (e.g. solve_store_eqs) that leaves them in a shape
    # this pass can't dissect is a bug — not a silent missed
    # opportunity. Fail loudly with the survivor names so the regression
    # is obvious.
    # Walk every assert's free variables. Any 2D+ array symbol referenced
    # (whether declared or auto-redeclared later by
    # `_ensure_declarations_for_asserts`) breaks the contract. solve_store_eqs's
    # cascading substitution can produce nested `(store 2d-base k v)`
    # expressions that flatten's walk_equals can't split (it requires at
    # least one bare flattenable symbol on a side), so 2D symbols silently
    # survive. Catch that here.
    fvo = get_env().fvo
    survivor_set: set[str] = set()
    for cmd in smt_script.commands:
        if cmd.name != "assert":
            continue
        for sym in fvo.get_free_variables(cmd.args[0]):
            if not (hasattr(sym, "is_symbol") and sym.is_symbol()):
                continue
            t = sym.get_type()
            if not t.is_array_type():
                continue
            elem_t = t.elem_type if hasattr(t, "elem_type") else t.param_types[0]
            if elem_t.is_array_type():
                survivor_set.add(sym.symbol_name())
    if survivor_set:
        survivors = sorted(survivor_set)
        raise AssertionError(
            f"flatten_outer_array: {len(survivors)} 2D+ array symbol(s) "
            f"still referenced in asserts after the pass: {survivors[:10]}"
            + (f" (+{len(survivors)-10} more)" if len(survivors) > 10 else "")
        )

    return smt_script


def _flatten_one_round(smt_script: script.SmtLibScript) -> dict:
    """Run one round of flattening. Returns counts as a dict.

    A "round" picks all flatten-eligible top-level array decls, performs
    the per-k split + rewrite once, and returns. The outer driver
    iterates this until no decl is flatten-eligible.
    """
    outer_decls = _collect_outer_decls(smt_script)
    if not outer_decls:
        return {"flattened": 0, "new_inner_arrays": 0, "asserts_rewritten": 0, "ineligible": 0}

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
        return {"flattened": 0, "new_inner_arrays": 0,
                "asserts_rewritten": 0, "ineligible": len(ineligible)}

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

    return {
        "flattened": len(eligible),
        "new_inner_arrays": len(new_inner_syms),
        "asserts_rewritten": rewritten_asserts,
        "ineligible": len(ineligible),
    }
