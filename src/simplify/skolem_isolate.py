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
    Group the unpinned int/bool qvars into connected components by
    co-occurrence in a body disjunct. A component is a *closed island* iff no
    disjunct mentioning any of its members also mentions a variable outside the
    component (an outer free variable, an already-pinned qvar, or a
    non-int/bool qvar). For a closed island ``S``:

        F unsat  ≡  ∀S, rest. ⋁_i D_i(S) ∨ E(rest)

    where the ``D_i`` are exactly the island's disjuncts and (by closedness)
    depend only on ``S`` — never on ``rest``. The existential ``∃S. ⋀_i
    ¬D_i(S)`` therefore decouples from ``rest``: any one satisfying assignment
    ``w`` of ``⋀_i ¬D_i`` is a uniform witness for *every* assignment of
    ``rest``. Pinning every member of ``S`` to its value under ``w`` does not
    lose unsat, and — because the island shares nothing with ``rest`` — does
    not introduce a spurious sat either.

    This generalizes the historical single-variable rule (each disjunct
    mentions exactly one qvar) to whole islands. The two failure modes the old
    strict gate guarded against are exactly the *non-closed* cases and are
    still rejected here:

    * A disjunct mentioning a qvar **and an outer free variable** ``x`` makes
      ``D_i(q, x)`` depend on ``x``; the probe's one-shot model gives a witness
      valid only for the ``x*`` it picked. The qvar is tainted ⇒ not pinned.
      (Regression: ``after-memory-N-isinput`` on
      ``apc_candidate_2099512_031_low_degree_bus-…_032_inlining.completeness``.)

    * A disjunct mentioning a qvar **and another qvar that is itself coupled to
      the outside** (transitively reaches an outer var or a pinned qvar) is in
      a tainted component ⇒ not pinned. A pin from one model would only
      establish the body at the probe's choice of the other qvar, not the value
      the rest of the formula forces on it.

    Note that two qvars sharing a disjunct is *not* by itself disqualifying:
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
        fv = d.get_free_variables()
        cset = [q for q in cand if q in fv]
        if not cset:
            continue
        disj_cands.append((cset, d))
        for other in cset[1:]:
            union(cset[0], other)
        if fv - cand:  # mentions an outer var / pinned qvar / non-int-bool qvar
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
