"""SMT-backed strengthening for small finite integer domains (choice/or-eq)."""
from __future__ import annotations

import logging
from typing import Optional

from pysmt.exceptions import SolverReturnedUnknownResultError

from ..report.action import Action
from ..smt.utils import *
from ..utils.stats import stats_dump

logger = logging.getLogger(__name__)

_MAX_VALUES = 3
_MAX_PAIRS = 20
_MAX_CLUSTER_ASSERTS = 100
_MAX_CLUSTER_FLAG_VARS = 16
_SOLVER_OPTS = {"rlimit": 1000000}

def _cluster_assertions(
    assertions: list[FNode], cluster: frozenset[FNode]
) -> list[FNode]:
    return [a for a in assertions if a.get_free_variables() <= cluster]


def _const_pinned_in(f: FNode) -> set[FNode]:
    if f.is_equals():
        a, b = f.args()
        if a.is_symbol() and a.get_type().is_int_type() and b.is_int_constant():
            return {a}
        if b.is_symbol() and b.get_type().is_int_type() and a.is_int_constant():
            return {b}
        return set()
    if f.is_and():
        out: set[FNode] = set()
        for arg in f.args():
            out |= _const_pinned_in(arg)
        return out
    return set()


def _flag_cluster(
    seed: FNode,
    assertions: list[FNode],
    choices: dict[FNode, list[int]],
) -> frozenset[FNode]:
    """Flag variables connected to ``seed`` via choice/pinned-only assertions."""
    cluster: set[FNode] = {seed}
    choice_syms = set(choices.keys())
    changed = True
    while changed:
        changed = False
        for a in assertions:
            if not cluster.intersection(a.get_free_variables()):
                continue
            new_pins = _const_pinned_in(a)
            if not new_pins <= cluster:
                cluster |= new_pins
                changed = True
        for a in assertions:
            fvs = {
                v
                for v in a.get_free_variables()
                if v.is_symbol() and v.get_type().is_int_type()
            }
            if not cluster.intersection(fvs):
                continue
            extras = fvs - cluster
            if extras <= choice_syms:
                new = extras - cluster
                if new:
                    cluster |= new
                    changed = True
    return frozenset(cluster)


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


def _choices_in_assertion(f: FNode) -> list[tuple[FNode, FNode, tuple[int, ...]]]:
    """Return ``(sym, or_node, values)`` for each choice constraint in ``f``."""
    parsed = _parse_or_equalities(f)
    if parsed is not None:
        sym, vals = parsed
        return [(sym, f, vals)]
    if not f.is_and():
        return []
    or_parts: dict[FNode, tuple[FNode, tuple[int, ...]]] = {}
    for arg in f.args():
        p = _parse_or_equalities(arg)
        if p is not None:
            sym, vals = p
            or_parts[sym] = (arg, vals)
    return [(sym, or_node, vals) for sym, (or_node, vals) in or_parts.items()]


def _collect_choices(assertions: list[FNode], max_n: int) -> dict[FNode, list[int]]:
    """Map each choice variable to probe candidate values (non-singleton, <= max_n)."""
    raw: dict[FNode, list[int]] = {}
    for a in assertions:
        for sym, _, vals in _choices_in_assertion(a):
            if not sym.is_symbol() or not sym.get_type().is_int_type():
                continue
            cur = raw.setdefault(sym, [])
            for v in vals:
                if v not in cur:
                    cur.append(v)
            cur.sort()
    return {sym: vals for sym, vals in raw.items() if 1 < len(vals) <= max_n}


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


def _probe_cluster(
    solver: Solver,
    cluster_choices: dict[FNode, list[int]],
    batch: list[FNode],
) -> dict[str, int]:
    outcomes = {"probes_sat": 0, "probes_unsat": 0, "probes_unknown": 0, "excluded": 0}
    for sym, vals in sorted(cluster_choices.items(), key=lambda kv: str(kv[0])):
        for v in vals:
            eq = Equals(sym, Int(v))
            r = _probe(solver, eq)
            tag = {True: "sat", False: "unsat", None: "unknown"}[r]
            logger.info("domain_probe: probe (= %s %s) -> %s", sym, v, tag)
            if tag == "sat":
                outcomes["probes_sat"] += 1
            elif tag == "unsat":
                outcomes["probes_unsat"] += 1
            else:
                outcomes["probes_unknown"] += 1
            if r is False:
                ne = Not(eq)
                if ne not in batch:
                    batch.append(ne)
                    solver.add_assertion(ne)
                    outcomes["excluded"] += 1
                    logger.info("domain_probe: exclude -> assert %s", ne)
    return outcomes


def simplify_domain_probe(
    smt_script: script.SmtLibScript,
    subaction: Action,
) -> script.SmtLibScript:
    total_added = 0
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    probe_stats: dict = {"base_asserts": len(assertions)}

    if not assertions:
        stats_dump("domain_probe", probe_stats)
        return smt_script

    choices = _collect_choices(assertions, _MAX_VALUES)
    probe_stats["choice_symbols"] = len(choices)
    if not choices:
        probe_stats.update({"pairs_probed": 0, "clusters_probed": 0})
        stats_dump("domain_probe", probe_stats)
        return smt_script

    try:
        insert_at = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )
        remaining = set(choices.keys())
        symbols_probed = 0
        clusters_probed = 0
        flag_vars_total = 0
        flag_local_total = 0

        logger.info(
            "domain_probe: start (%d base asserts, %d candidate(s), "
            "max %d symbol(s), solver rlimit %s)",
            len(assertions),
            len(choices),
            _MAX_PAIRS,
            _SOLVER_OPTS["rlimit"],
        )

        batch: list[FNode] = []
        cluster_stats: list[dict] = []
        while remaining and symbols_probed < _MAX_PAIRS:
            seed = min(remaining, key=str)
            cluster = _flag_cluster(seed, assertions, choices)
            remaining -= cluster
            cluster_choices = {s: choices[s] for s in cluster if s in choices}
            if not cluster_choices:
                continue

            n_syms = len(cluster_choices)
            if symbols_probed + n_syms > _MAX_PAIRS:
                cluster_choices = dict(
                    sorted(cluster_choices.items(), key=lambda kv: str(kv[0]))[
                        : _MAX_PAIRS - symbols_probed
                    ]
                )

            rel = _cluster_assertions(assertions, cluster)
            if len(cluster) > _MAX_CLUSTER_FLAG_VARS or len(rel) > _MAX_CLUSTER_ASSERTS:
                logger.info(
                    "domain_probe: skip cluster seed %s (%d flag var(s), %d assert(s))",
                    seed,
                    len(cluster),
                    len(rel),
                )
                continue
            clusters_probed += 1
            symbols_probed += len(cluster_choices)
            flag_vars_total += len(cluster)
            flag_local_total = len(rel)

            logger.info(
                "domain_probe: cluster %d seed %s vars %s (%d assert(s))",
                clusters_probed,
                seed,
                sorted(map(str, cluster)),
                len(rel),
            )

            with Solver(logic=ALL, solver_options=_SOLVER_OPTS) as solver:
                for f in rel:
                    solver.add_assertion(f)
                cluster_outcomes = _probe_cluster(solver, cluster_choices, batch)
            cluster_stats.append({
                "index": clusters_probed,
                "n_vars": len(cluster_choices),
                "n_flag_vars": len(cluster),
                "n_asserts": len(rel),
                **cluster_outcomes,
            })

        probe_stats.update({
            "pairs_probed": symbols_probed,
            "clusters_probed": clusters_probed,
            "flag_vars": flag_vars_total,
            "flag_local_asserts": flag_local_total,
            "clusters": cluster_stats,
        })
        if len(choices) > symbols_probed:
            logger.info(
                "domain_probe: probed %d of %d candidate symbol(s) in %d cluster(s)",
                symbols_probed,
                len(choices),
                clusters_probed,
            )

        if batch:
            for f in batch:
                smt_script.commands.insert(
                    insert_at,
                    script.SmtLibCommand(name="assert", args=[f]),
                )
                insert_at += 1
            total_added += len(batch)
            logger.info("domain_probe: inserted %d assert(s)", len(batch))
        else:
            logger.info("domain_probe: no new facts")

        logger.info(
            "domain_probe: done (%d new assert(s) in script)",
            total_added,
        )
        return smt_script
    except Exception as e:
        logger.info("domain_probe: solver error, stopping: %s", e)
        return smt_script
    finally:
        probe_stats["added_facts"] = total_added
        stats_dump("domain_probe", probe_stats)
