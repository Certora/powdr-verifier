"""SMT-backed strengthening for small finite integer domains (interval + or-eq)."""
from __future__ import annotations

import logging
from collections import defaultdict
from typing import TYPE_CHECKING, Optional

from pysmt.exceptions import SolverReturnedUnknownResultError

from ..smt.utils import *

if TYPE_CHECKING:
    from ..report.action import Action
from .intervals.domain import IntDomain, IntInterval
from .intervals.reasoner import IntervalReasoner

logger = logging.getLogger(__name__)

_MAX_VALUES = 3
_MAX_PAIRS = 20
_SOLVER_OPTS = {"rlimit": 1000000}

# TODO: hacky filter for specific variables

def _flag_local_assertions(
    assertions: list[FNode], flag_vars: frozenset[FNode]
) -> list[FNode]:
    """Constraints whose free variables are *all* small-domain ("flag-local").

    A flag's pinned value is determined by its flag-local polynomial structure
    — the domain cubic ``f·(f-1)·(f-2) ≡ 0`` (or ``f·(f-1) ≡ 0``) and the
    group's one-hot / sum constraint — not by the wide bus interactions the
    flag gates (those mention data columns ``a/b/c`` and pull a 178s nonlinear
    solve into each probe). Slicing to constraints whose free vars are all
    flag-like keeps exactly the structural-lever system (cf.
    ``flag-pinning-structural-lever``) and makes each probe tiny.

    Sound w.r.t. pinning: probing a *subset* of constraints can only return
    ``unsat`` when the full set is ``unsat`` (sound pin) and otherwise declines
    to pin (conservative). Flags determined only by global interaction are
    missed — but those are precisely the probes that are too expensive anyway.
    """
    return [a for a in assertions if a.get_free_variables() <= flag_vars]


def _small_domain_vars(
    assertions: list[FNode],
    reasoner: "IntervalReasoner",
    or_map: dict[FNode, set[int]],
    max_n: int,
) -> frozenset[FNode]:
    """Int symbols with a known finite domain of <= ``max_n`` values (flag-like)."""
    flags: set[FNode] = set()
    seen: set[FNode] = set()
    for a in assertions:
        for v in a.get_free_variables():
            if v in seen:
                continue
            seen.add(v)
            if not (v.is_symbol() and v.get_type().is_int_type()):
                continue
            vs = _finite_values(reasoner.get_domain(v), max_n)
            if (vs is not None and len(vs) <= max_n) or (
                v in or_map and len(or_map[v]) <= max_n
            ):
                flags.add(v)
    return frozenset(flags)


def _finite_values(dom: IntDomain, max_n: int) -> Optional[list[int]]:
    if dom.is_bottom():
        return None
    out: list[int] = []
    for iv in dom.parts:
        if iv.lo is None or iv.hi is None:
            return None
        for x in range(iv.lo, iv.hi + 1):
            out.append(x)
            if len(out) > max_n:
                return None
    return out


def _parse_or_equalities(f: FNode) -> Optional[tuple[FNode, tuple[int, ...]]]:
    if not f.is_or():
        return None
    sym: Optional[FNode] = None
    vals: list[int] = []
    for d in f.args():
        if not d.is_equals():
            return None
        a, b = d.args()
        if a.is_symbol() and b.is_int_constant():
            cur_sym, c = a, int(b.constant_value())
        elif b.is_symbol() and a.is_int_constant():
            cur_sym, c = b, int(a.constant_value())
        else:
            return None
        if sym is None:
            sym = cur_sym
        elif sym != cur_sym:
            return None
        vals.append(c)
    if sym is None or not vals:
        return None
    return sym, tuple(sorted(set(vals)))


def _walk_collect_or_eq(f: FNode, acc: dict[FNode, set[int]]) -> None:
    stack = [f]
    seen: set[int] = set()
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen.add(id(n))
        p = _parse_or_equalities(n)
        if p is not None:
            sym, vals = p
            acc[sym].update(vals)
        if n.is_quantifier():
            stack.append(n.arg(0))
            continue
        stack.extend(n.args())


def _collect_or_map(formulae: list[FNode]) -> dict[FNode, set[int]]:
    or_map: dict[FNode, set[int]] = defaultdict(set)
    for a in formulae:
        _walk_collect_or_eq(a, or_map)
    return or_map


def _candidate_pairs(
    reasoner: IntervalReasoner, or_map: dict[FNode, set[int]]
) -> list[tuple[FNode, list[int]]]:
    syms: set[FNode] = set(reasoner.env.keys()) | {s for s in or_map if s.is_symbol()}
    out: list[tuple[FNode, list[int]]] = []
    for sym in syms:
        if not sym.is_symbol() or not sym.get_type().is_int_type():
            continue
        dom = reasoner.get_domain(sym)
        if sym in or_map and len(or_map[sym]) <= _MAX_VALUES:
            od = IntDomain.from_intervals(IntInterval.const(v) for v in sorted(or_map[sym]))
            dom = dom.intersect(od)
        vs = _finite_values(dom, _MAX_VALUES)
        if not vs or len(vs) > _MAX_VALUES or len(vs) == 1:
            continue
        out.append((sym, vs))
    return out


def _rank_candidates(
    pairs: list[tuple[FNode, list[int]]],
    reasoner: IntervalReasoner,
    or_syms: set[FNode],
) -> list[tuple[FNode, list[int]]]:
    """Prefer tightened int vars, then explicit (or (= v …)) sources, then smaller domains."""
    tightened = reasoner.tightened_symbols

    def rank(item: tuple[FNode, list[int]]) -> tuple[int, int, int, str]:
        sym, vals = item
        return (
            0 if sym in tightened else 1,
            0 if sym in or_syms else 1,
            len(vals),
            str(sym),
        )

    return sorted(pairs, key=rank)


def _probe(solver: Solver, assumption: FNode) -> Optional[bool]:
    solver.push()
    solver.add_assertion(assumption)
    try:
        return solver.solve()
    except SolverReturnedUnknownResultError:
        logger.info("domain_probe: probe %s -> unknown (skipped)", assumption)
        return None
    finally:
        solver.pop()


def simplify_domain_probe(
    smt_script: script.SmtLibScript,
    subaction: Optional["Action"] = None,
) -> script.SmtLibScript:
    total_added = 0
    extra: dict = {}
    try:
        assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
        extra["base_asserts"] = len(assertions)
        if not assertions:
            return smt_script

        insert_at = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )

        accumulated: list[FNode] = []

        base_reasoner = IntervalReasoner()
        base_reasoner.assume_all(assertions)
        or_map = _collect_or_map(assertions)
        or_syms = {s for s in or_map if s.is_symbol() and s.get_type().is_int_type()}
        all_pairs = _candidate_pairs(base_reasoner, or_map)
        ranked_all = _rank_candidates(all_pairs, base_reasoner, or_syms)
        extra["ranked_candidate_pairs"] = len(ranked_all)

        logger.info(
            "domain_probe: start (%d base asserts, %d ranked candidate(s), "
            "max %d pair(s), solver rlimit %s)",
            len(assertions),
            len(ranked_all),
            _MAX_PAIRS,
            _SOLVER_OPTS["rlimit"],
        )

        if not ranked_all:
            logger.info("domain_probe: no candidates (non-singleton domains), done")
            extra["pairs_probed"] = 0
            return smt_script

        pairs = ranked_all[:_MAX_PAIRS]
        extra["pairs_probed"] = len(pairs)
        if len(ranked_all) > len(pairs):
            logger.info(
                "domain_probe: probing %d of %d ranked candidate pair(s)",
                len(pairs),
                len(ranked_all),
            )

        cand = ", ".join(
            f"{sym} in {{{','.join(map(str, vals))}}}"
            for sym, vals in pairs
        )
        logger.info("domain_probe: %d pair(s): %s", len(pairs), cand)

        # Flag-local slice: probe pins against constraints involving only
        # small-domain vars (cubics + group one-hot/sum), not the wide bus
        # interactions a flag gates. Same for every candidate, so compute once.
        flag_vars = _small_domain_vars(assertions, base_reasoner, or_map, _MAX_VALUES)
        flag_local = _flag_local_assertions(assertions, flag_vars)
        extra["flag_vars"] = len(flag_vars)
        extra["flag_local_asserts"] = len(flag_local)
        logger.info(
            "domain_probe: flag-local slice = %d assert(s) over %d flag var(s)",
            len(flag_local),
            len(flag_vars),
        )

        try:
            batch: list[FNode] = []
            for sym, vals in pairs:
                rel = flag_local
                logger.info(
                    "domain_probe: symbol %s: %d flag-local of %d assert(s)",
                    sym,
                    len(rel),
                    len(assertions),
                )
                with Solver(logic=QF_UFNIA, solver_options=_SOLVER_OPTS) as solver:
                    for f in rel:
                        solver.add_assertion(f)
                    for v in vals:
                        eq = Equals(sym, Int(v))
                        r = _probe(solver, eq)
                        tag = {True: "sat", False: "unsat", None: "unknown"}[r]
                        logger.info(
                            "domain_probe: probe (= %s %s) -> %s",
                            sym,
                            v,
                            tag,
                        )
                        if r is False:
                            ne = Not(eq)
                            if not any(ne == x for x in batch + accumulated):
                                batch.append(ne)
                                solver.add_assertion(ne)
                                logger.info(
                                    "domain_probe: exclude -> assert %s",
                                    ne,
                                )
            if batch:
                for f in batch:
                    smt_script.commands.insert(
                        insert_at,
                        script.SmtLibCommand(name="assert", args=[f]),
                    )
                    insert_at += 1
                    accumulated.append(f)
                total_added += len(batch)
                logger.info(
                    "domain_probe: inserted %d assert(s)",
                    len(batch),
                )
            else:
                logger.info("domain_probe: no new facts")
        except Exception as e:
            logger.info("domain_probe: solver error, stopping: %s", e)

        logger.info(
            "domain_probe: done (%d new assert(s) in script)",
            total_added,
        )

        return smt_script
    finally:
        if subaction is not None:
            subaction += {"added_facts": total_added, **extra}
