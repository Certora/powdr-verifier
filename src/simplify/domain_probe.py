"""SMT-backed strengthening for small finite integer domains (interval + or-eq)."""
from __future__ import annotations

import logging
from collections import defaultdict
from typing import Optional

from pysmt.exceptions import SolverReturnedUnknownResultError

from ..smt.utils import *
from .intervals.domain import IntDomain, IntInterval
from .intervals.reasoner import IntervalReasoner

logger = logging.getLogger(__name__)

_MAX_VALUES = 3
_MAX_PAIRS = 20
_SOLVER_OPTS = {"timeout": 500}


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


def simplify_domain_probe(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        return smt_script

    insert_at = next(
        (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
        len(smt_script.commands),
    )

    accumulated: list[FNode] = []
    total_added = 0

    base_reasoner = IntervalReasoner()
    base_reasoner.assume_all(assertions)
    or_map = _collect_or_map(assertions)
    or_syms = {s for s in or_map if s.is_symbol() and s.get_type().is_int_type()}
    all_pairs = _candidate_pairs(base_reasoner, or_map)
    ranked_all = _rank_candidates(all_pairs, base_reasoner, or_syms)

    logger.info(
        "domain_probe: start (%d base asserts, %d ranked candidate(s), "
        "max %d pair(s), solver timeout %sms)",
        len(assertions),
        len(ranked_all),
        _MAX_PAIRS,
        _SOLVER_OPTS["timeout"],
    )

    if not ranked_all:
        logger.info("domain_probe: no candidates (non-singleton domains), done")
        return smt_script

    pairs = ranked_all[:_MAX_PAIRS]
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

    try:
        with Solver(logic=QF_UFNIA, solver_options=_SOLVER_OPTS) as solver:
            for f in assertions:
                solver.add_assertion(f)

            batch: list[FNode] = []
            for sym, vals in pairs:
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
                    elif r is True:
                        if not any(eq == x for x in batch + accumulated):
                            batch.append(eq)
                            solver.add_assertion(eq)
                            logger.info(
                                "domain_probe: pin -> assert %s",
                                eq,
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
