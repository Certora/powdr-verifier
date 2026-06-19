"""Isolation skolem contributor (last in the skolem chain).

Field-bounded QF_UFNIA probes pin quantified int/bool variables that form a
*closed island*: a set of qvars whose constraint-disjuncts mention only qvars
from that same set (no outer free variable, no already-pinned qvar, no
non-int/bool qvar). Such an island is decoupled from the rest of the formula,
so a single satisfying assignment of its constraints is a uniform witness —
all members can be pinned from one model. Runs after rules, derived, witness,
and same-name contributors.
"""
import logging

from pysmt.exceptions import SolverReturnedUnknownResultError

from ..smt.utils import *

# Bound the island probe with z3's ``rlimit`` (a deterministic count of internal
# work units) rather than a wall-clock ``timeout``. rlimit is reproducible
# across machines and runs and is unaffected by cold-process JIT/init cost — a
# wall-clock timeout made the first query in a fresh process flakily return
# ``unknown``. Real islands are cheap (the guest-keccak diff-marker cluster
# probe costs ~27k units); a few million gives large margin while still
# bounding a runaway probe to deterministic, terminating work.
_ISLAND_RLIMIT = 5_000_000


def _qvar_conjuncts(d: FNode, cand: frozenset) -> list[FNode]:
    """Top-level conjuncts of ``d`` that mention a candidate qvar.

    A qvar inside an ``And``-disjunct is coupled to a sibling conjunct only if
    they share an *atom*; conjuncts that mention no candidate qvar are separable
    (they ride along multiplicatively, outside the ``∀x.R(x)`` factor of
    ``∀x.(E ∨ (R(x) ∧ S(rest))) = E ∨ (S(rest) ∧ ∀x.R(x))``) and so are
    irrelevant to the qvar's island. For a non-``And`` disjunct this returns
    ``[d]``, i.e. the historical whole-disjunct behaviour.
    """
    conjs = d.args() if d.is_and() else (d,)
    return [c for c in conjs if c.get_free_variables() & cand]


def _model_value(model, var: FNode) -> FNode | None:
    """Look up ``var`` in a PySMT model mapping; ``None`` if absent."""
    for k, v in model:
        if k == var:
            return v
    return None


def _solve_island(falsify_parts: list[FNode], members: set[FNode]):
    """Solve ``⋀ falsify_parts`` under field bounds on int members.

    ``falsify_parts`` are the negations of the island's body disjuncts, i.e.
    the island's actual constraints. Returns the PySMT model if satisfiable,
    else ``None``.
    """
    try:
        with Solver(logic=QF_UFNIA, solver_options={"rlimit": _ISLAND_RLIMIT}) as solver:
            for v in members:
                if v.get_type().is_int_type():
                    solver.add_assertion(field_symbol(v))
            for part in falsify_parts:
                solver.add_assertion(part)
            if not solver.solve():
                return None
            return solver.get_model()
    except SolverReturnedUnknownResultError:
        # rlimit exhausted (genuinely hard probe): leave the island unpinned.
        return None
    except Exception as e:
        logging.debug(f"island isolate solve failed for {sorted(map(str, members))}: {e}")
        return None


def contribute(skolem_map, body: FNode) -> None:
    """Pin unpinned int/bool qvars that form closed islands of the forall body.

    Soundness invariant
    --------------------
    For each body disjunct ``D_i`` keep only its **qvar-relevant conjuncts**
    ``R_i`` (split ``D_i`` on top-level ``And``; drop conjuncts that mention no
    candidate qvar). The dropped conjuncts ``S_i`` are outer-only and separable:
    ``∀S.(E ∨ (R_i(S) ∧ S_i(rest))) = E ∨ (S_i(rest) ∧ ∀S.R_i(S))`` puts ``S_i``
    *outside* the ``∀S.R_i`` factor, so it never affects whether the universal
    collapses. Group qvars into components by co-occurrence across the ``R_i``.
    A component is a *closed island* iff no ``R_i`` mentioning a member also
    mentions a variable outside the component (an outer free variable, an
    already-pinned qvar, or a non-int/bool qvar). For a closed island ``S``:

        F unsat  ≡  ∀S, rest. ⋁_i (R_i(S) ∧ S_i(rest)) ∨ E(rest)

    where (by closedness) each ``R_i`` depends only on ``S`` — never on
    ``rest``. A satisfying assignment ``w`` of ``⋀_i ¬R_i(S)`` makes every
    ``R_i(w)`` false, so the island's disjuncts vanish *for every* ``rest``
    (``R_i(w) ∧ S_i = false`` regardless of ``S_i``) and ``∀S.R_i`` is false
    (witnessed by ``w``). Pinning every member of ``S`` to its value under ``w``
    is therefore exact: it neither loses unsat nor introduces a spurious sat.
    Skolemization commits each qvar to a single value, so we need one model of
    ``⋀_i ¬R_i`` — distributing ``∀`` over the conjunction does not let us pin
    per-conjunct (each conjunct would want a different witness).

    This generalizes the historical single-variable rule (each disjunct
    mentions exactly one qvar) to whole islands, and the per-conjunct split
    further admits qvars buried in an ``And`` alongside outer-only siblings
    (the powdr ``remove_free`` shape: ``(P(x) ∧ Q(outer))``). The two failure
    modes the old strict gate guarded against are exactly the *non-closed*
    cases — where the qvar shares an **atom** (not merely an ``And``) with the
    outside — and are still rejected here:

    * A qvar-relevant conjunct mentioning a qvar **and an outer free variable**
      ``x`` makes ``R_i(q, x)`` depend on ``x``; the probe's one-shot model
      gives a witness valid only for the ``x*`` it picked. The qvar is tainted
      ⇒ not pinned. (Regression: ``after-memory-N-isinput`` on
      ``apc_candidate_2099512_031_low_degree_bus-…_032_inlining.completeness``.)

    * A qvar-relevant conjunct mentioning a qvar **and another qvar that is
      itself coupled to the outside** (transitively reaches an outer var or a
      pinned qvar) is in a tainted component ⇒ not pinned. A pin from one model
      would only establish the body at the probe's choice of the other qvar,
      not the value the rest of the formula forces on it.

    Note that two qvars sharing a conjunct is *not* by itself disqualifying:
    when their whole component is closed (the
    ``diff_marker__*`` / ``diff_val_*`` cluster left behind by powdr's
    ``remove_free``, for instance), they are pinned jointly from one model.

    See ``tests/simplify/test_isolate.py``.
    """
    if not body.is_or():
        return

    qvars = skolem_map.qvars
    cand = frozenset(
        q for q in qvars
        if not skolem_map.is_pinned(q)
        and (q.get_type().is_int_type() or q.get_type().is_bool_type())
    )
    if not cand:
        return

    # Union-find over candidate qvars; taint a candidate if it shares a
    # disjunct with anything outside `cand`.
    parent: dict[FNode, FNode] = {q: q for q in cand}

    def find(x: FNode) -> FNode:
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    def union(a: FNode, b: FNode) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    tainted: set[FNode] = set()
    disj_cands: list[tuple[list[FNode], FNode]] = []
    for d in body.args():
        cset = [q for q in cand if q in d.get_free_variables()]
        if not cset:
            continue
        # Only the conjuncts that actually mention a candidate qvar matter for
        # the island; outer-only sibling conjuncts (joined by AND) are separable
        # and do not couple the qvar to the rest of the formula. We taint and
        # solve over `rel = R(x)` rather than the whole disjunct `d`.
        rel = _qvar_conjuncts(d, cand)
        rel_fv = frozenset().union(*(c.get_free_variables() for c in rel))
        relevant = And(*rel)
        disj_cands.append((cset, relevant))
        for other in cset[1:]:
            union(cset[0], other)
        if rel_fv - cand:  # a qvar-conjunct mentions an outer / pinned / non-int-bool var
            tainted.update(cset)

    if not disj_cands:
        return

    members_by_root: dict[FNode, set[FNode]] = {}
    disjuncts_by_root: dict[FNode, list[FNode]] = {}
    for q in cand:
        members_by_root.setdefault(find(q), set()).add(q)
    for cset, d in disj_cands:
        disjuncts_by_root.setdefault(find(cset[0]), []).append(d)
    tainted_roots = {find(q) for q in tainted}

    for root, disjuncts in disjuncts_by_root.items():
        if root in tainted_roots:
            continue
        members = members_by_root[root]
        falsify_parts = [Not(d) for d in disjuncts]
        model = _solve_island(falsify_parts, members)
        if model is None:
            continue
        for q in members:
            val = _model_value(model, q)
            if val is None:
                # Unconstrained within the island: any value is a valid
                # uniform witness; default to the type's zero.
                val = Int(0) if q.get_type().is_int_type() else FALSE()
            skolem_map.pin(q, val, source="isolate")
