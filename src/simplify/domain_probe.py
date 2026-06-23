"""SMT-backed strengthening for small finite integer domains (choice/or-eq)."""
from __future__ import annotations

import logging
from typing import Optional

from pysmt.exceptions import SolverReturnedUnknownResultError

from ..report.action import Action
from ..smt.utils import *

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
    choices: dict[FNode, list[int]],
    max_n: int,
) -> frozenset[FNode]:
    """All int symbols treated as small-domain for flag-local slicing."""
    flags: set[FNode] = set(choices.keys())
    for a in assertions:
        if not flags.intersection(a.get_free_variables()):
            continue
        for arg in (a.args() if a.is_and() else [a]):
            if not arg.is_equals():
                continue
            x, y = arg.args()
            if x.is_symbol() and x.get_type().is_int_type() and y.is_int_constant():
                flags.add(x)
            elif y.is_symbol() and y.get_type().is_int_type() and x.is_int_constant():
                flags.add(y)
    return frozenset(flags)


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


def simplify_domain_probe(
    smt_script: script.SmtLibScript,
    subaction: Action,
) -> script.SmtLibScript:
    total_added = 0

    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    subaction += {"base_asserts": len(assertions)}
    if not assertions:
        return smt_script

    choices = _collect_choices(assertions, _MAX_VALUES)
    subaction += {"choice_symbols": len(choices)}
    if not choices:
        subaction += {"pairs_probed": 0}
        return smt_script

    try:

        insert_at = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )

        accumulated: list[FNode] = []

        logger.info(
            "domain_probe: start (%d base asserts, %d candidate(s), "
            "max %d pair(s), solver rlimit %s)",
            len(assertions),
            len(choices),
            _MAX_PAIRS,
            _SOLVER_OPTS["rlimit"],
        )

        pairs = list(choices.items())[:_MAX_PAIRS]
        subaction += {"pairs_probed": len(pairs)}
        if len(choices) > len(pairs):
            logger.info(
                "domain_probe: probing %d of %d candidate pair(s)",
                len(pairs),
                len(choices),
            )

        cand = ", ".join(
            f"{sym} in {{{','.join(map(str, vals))}}}"
            for sym, vals in pairs
        )
        logger.info("domain_probe: %d pair(s): %s", len(pairs), cand)

        flag_vars = _small_domain_vars(assertions, choices, _MAX_VALUES)
        flag_local = _flag_local_assertions(assertions, flag_vars)
        subaction += {
            "flag_vars": len(flag_vars),
            "flag_local_asserts": len(flag_local),
        }
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
                with Solver(logic=ALL, solver_options=_SOLVER_OPTS) as solver:
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
        subaction += {"added_facts": total_added}
