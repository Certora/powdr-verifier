"""Helpers for the plain (busat-style) memory permutation encoding.

``cone_of_influence`` narrows main constraints to those touching seed variables.
``plain_memory_const_key_io_hints`` adds first/last-occurrence input/output pins
for constant (address_space, pointer) keys. ``plain_memory_presolve`` alternates boolean unit propagation, dropping match
variables already fixed at top level, and SMT checks for further implied units,
using optional ``context`` (e.g. timestamp COI) only inside the working formula.
``plain_memory_presolve_new`` does the same but uses a fresh solver per literal, with
full timestamp COI from ``coi_constraints`` and a one-step match-variable COI from
the permutation conjuncts.
"""
import logging
import time
from collections.abc import Callable
from typing import Any

from ..utils.args import ARGS
from ..smt.utils import *


def cone_of_influence(constraints: list[FNode], variables: set[FNode]) -> list[FNode]:
    """Return constraints in the cone-of-influence closure of ``variables``."""
    active: set[FNode] = set(variables)
    picked: set[FNode] = set()
    while True:
        added = False
        for c in constraints:
            if c in picked:
                continue
            if not active.isdisjoint(c.get_free_variables()):
                picked.add(c)
                active |= c.get_free_variables()
                added = True
        if not added:
            break
    return [c for c in constraints if c in picked]


def cone_of_influence_one_step(
    constraints: list[FNode], variables: set[FNode]
) -> list[FNode]:
    """Return constraints mentioning at least one of ``variables`` (no fixpoint)."""
    return [
        c for c in constraints if not variables.isdisjoint(c.get_free_variables())
    ]


def coi_for_match_imply(
    coi_constraints: list[FNode],
    conjuncts: list[FNode],
    interactions: list[Any],
    match_indices: tuple[int, int],
    match_var: FNode,
) -> list[FNode]:
    """Context for implying a match literal between interactions ``match_indices``.

    Full COI of ``coi_constraints`` from the two interaction timestamps, plus a
    one-step COI of ``conjuncts`` from ``match_var``.
    """
    ts_vars: set[FNode] = frozenset.union(
        *[interactions[i].args[-1].get_free_variables() for i in match_indices]
    )
    full_ts_coi = cone_of_influence(coi_constraints, ts_vars)
    match_coi = cone_of_influence_one_step(conjuncts, {match_var})
    picked: set[FNode] = set()
    out: list[FNode] = []
    for c in full_ts_coi + match_coi:
        if c in picked:
            continue
        picked.add(c)
        out.append(c)
    return out


def boolean_propagate(conjuncts: list[FNode]) -> list[FNode]:
    """Top-level bool unit conjuncts become substitutions applied to the rest (fixpoint)."""
    literals: list[FNode] = []
    remaining = [keep_comment(f.simplify(), f) for f in conjuncts]
    substitutions: dict[FNode, FNode] = {}

    def record_literal(lit: FNode) -> bool:
        if lit.is_symbol(BOOL):
            sym, val = lit, TRUE()
        elif lit.is_not() and lit.arg(0).is_symbol(BOOL):
            sym, val = lit.arg(0), FALSE()
        else:
            return False
        if sym in substitutions:
            return False
        substitutions[sym] = val
        literals.append(lit)
        return True

    while True:
        new_binding = False
        next_remaining: list[FNode] = []
        for f in remaining:
            f = keep_comment(f.simplify(), f)
            if record_literal(f):
                new_binding = True
            elif not f.is_true():
                next_remaining.append(f)
        remaining = (
            [keep_comment(g.substitute(substitutions), g) for g in next_remaining]
            if substitutions
            else next_remaining
        )
        if not new_binding:
            break

    return literals + remaining


def plain_memory_const_key_io_hints(
    interactions: list[Any],
    is_input: Callable[[int], FNode],
    is_output: Callable[[int], FNode],
    mult: Callable[[int], FNode],
) -> list[FNode]:
    """Pin first (resp. last) occurrence of each constant (addr_space, ptr) as input (resp. output).

    When multiplicity is not identically zero, the first interaction in trace
    order with a given constant key is marked an input; the last such
    interaction is marked an output. Each scan stops at the first row whose
    address space or pointer is not an int constant.
    """
    n = len(interactions)
    if n == 0:
        return []
    p = ARGS().field_type.value

    def const_key(i: int) -> tuple[int, int] | None:
        a = interactions[i].args
        if len(a) < 2:
            return None
        as_, ptr = a[0], a[1]
        if not as_.is_int_constant() or not ptr.is_int_constant():
            return None
        return (as_.constant_value() % p, ptr.constant_value() % p)

    out: list[FNode] = []
    seen_in: set[tuple[int, int]] = set()
    for i in range(n):
        k = const_key(i)
        if k is None:
            break
        if k in seen_in:
            continue
        seen_in.add(k)
        msg = f"const-key first occurrence => input (interaction {i}, key {k})"
        logging.info("plain_memory_const_key_io_hints: %s", msg)
        out.append(
            with_comment(
                Implies(Not(field_eq(mult(i))), is_input(i)),
                msg,
            )
        )

    seen_out: set[tuple[int, int]] = set()
    for i in range(n - 1, -1, -1):
        k = const_key(i)
        if k is None:
            break
        if k in seen_out:
            continue
        seen_out.add(k)
        msg = f"const-key last occurrence => output (interaction {i}, key {k})"
        logging.info("plain_memory_const_key_io_hints: %s", msg)
        out.append(
            with_comment(
                Implies(Not(field_eq(mult(i))), is_output(i)),
                msg,
            )
        )
    return out


def _unit_bool_key(conjunct: FNode) -> tuple[FNode, bool] | None:
    s = conjunct.simplify()
    if s.is_symbol(BOOL):
        return (s, True)
    if s.is_not() and s.arg(0).is_symbol(BOOL):
        return (s.arg(0), False)
    return None


def _record_new_unit_prefix(
    working: list[FNode],
    units: dict[FNode, bool],
) -> bool:
    changed = False
    for c in working:
        k = _unit_bool_key(c)
        if k is None:
            break
        sym, pol = k
        if sym in units:
            assert units[sym] == pol, (sym, units[sym], pol)
            continue
        units[sym] = pol
        changed = True
    return changed


def _top_level_fixed_bool_symbols(working: list[FNode]) -> set[FNode]:
    """Bool symbols that appear as their own top-level conjunct (possibly negated)."""
    syms: set[FNode] = set()
    for c in working:
        k = _unit_bool_key(c)
        if k is not None:
            syms.add(k[0])
    return syms


def _fresh_is_valid(
    conjuncts: list[FNode],
    literals: list[FNode],
    *,
    log_prefix: str,
) -> FNode | None:
    """Return the first literal in ``literals`` entailed by ``conjuncts``, if any."""
    if not literals:
        return None
    try:
        with Solver(
            logic=logics.ALL,
            name="z3",
            incremental=True,
            solver_options={"rlimit": 10000000},
        ) as s:
            s.z3.set("timeout", 500)
            for c in conjuncts:
                s.add_assertion(c)
            for lit in literals:
                s.push()
                s.add_assertion(Not(lit))
                try:
                    if not s.solve():
                        return lit
                except SolverReturnedUnknownResultError:
                    logging.info("%s: is_valid unknown for %s", log_prefix, lit)
                except Exception:
                    logging.info("%s: is_valid failed for %s", log_prefix, lit)
                finally:
                    s.pop()
    except Exception:
        logging.info("%s: is_valid failed for %s", log_prefix, literals)
    return None


def _safe_is_valid(solver: Solver, f: FNode) -> bool | None:
    solver.z3.set("timeout", 200)
    solver.push()
    solver.add_assertion(Not(f))
    try:
        if solver.solve():
            return False
        return True
    except SolverReturnedUnknownResultError:
        logging.info("plain_memory_presolve: is_valid unknown for %s", f)
        return None
    except Exception:
        logging.info("plain_memory_presolve: is_valid failed for %s", f)
        return None
    finally:
        solver.pop()


def _collect_implied_top_level_literals(
    conjuncts: list[FNode], bool_vars: set[FNode]
) -> list[FNode]:
    """Entailed ``v`` / ``Not(v)`` for remaining ``bool_vars`` via incremental ``is_valid`` checks."""
    if not bool_vars:
        return []
    out: list[FNode] = []
    with Solver(
        logic=logics.ALL,
        name="z3",
        incremental=True,
        solver_options={"rlimit": 10000000},
    ) as s:
        for c in conjuncts:
            s.add_assertion(c)
        for v in list(bool_vars):
            nv = _safe_is_valid(s, Not(v))
            if nv is True:
                lit = Not(v)
                out.append(lit)
                logging.info("plain_memory_presolve: solver implied unit %s", lit)
                s.add_assertion(lit)
                continue
            pv = _safe_is_valid(s, v)
            if pv is True:
                out.append(v)
                logging.info("plain_memory_presolve: solver implied unit %s", v)
                s.add_assertion(v)
    return out


def plain_memory_presolve(
    conjuncts: list[FNode],
    bool_vars: set[FNode],
    *,
    context: list[FNode] | None = None,
) -> list[FNode]:
    """Learn unit bool facts for match variables; mutates ``bool_vars`` in place.

    ``context`` is included only in the internal working formula (not in the
    returned list). Returns new unit literals to add to the permutation side.
    """
    ctx = context or []
    t0 = time.monotonic()
    n_tracked0 = len(bool_vars)
    n_ctx = len(ctx)
    working = [*ctx, *conjuncts]
    units: dict[FNode, bool] = {}
    iterations = 0
    while True:
        iterations += 1
        changed = False
        working[:] = boolean_propagate(working)
        if _record_new_unit_prefix(working, units):
            changed = True
        n_before = len(bool_vars)
        bool_vars.difference_update(_top_level_fixed_bool_symbols(working))
        n_after_strip = len(bool_vars)
        if n_after_strip != n_before:
            changed = True

        new_lits = _collect_implied_top_level_literals(working, bool_vars)
        for lit in new_lits:
            k = _unit_bool_key(lit)
            if k is None:
                continue
            sym, pol = k
            if sym in units:
                assert units[sym] == pol, (sym, units[sym], pol)
                continue
            units[sym] = pol
        if new_lits:
            changed = True
            working[:] = new_lits + working
            bool_vars.difference_update(_top_level_fixed_bool_symbols(working))
        logging.debug(
            "plain_memory_presolve round %d: tracked=%d implied_lits=%d changed=%s",
            iterations,
            len(bool_vars),
            len(new_lits),
            changed,
        )
        if not changed:
            break
    out = [(sym if pol else Not(sym)).simplify() for sym, pol in units.items()]
    elapsed_ms = (time.monotonic() - t0) * 1000.0
    n_tracked1 = len(bool_vars)
    remaining = ", ".join(sorted(str(v) for v in bool_vars))
    logging.debug(
        "plain_memory_presolve: %.1f ms, %d rounds, tracked match_vars %d -> %d "
        "(%d fixed / dropped), %d learned unit literals for output, %d context conjuncts; "
        "remaining unknown match_vars (%d): %s",
        elapsed_ms,
        iterations,
        n_tracked0,
        n_tracked1,
        n_tracked0 - n_tracked1,
        len(out),
        n_ctx,
        n_tracked1,
        remaining if remaining else "(none)",
    )
    return out


def plain_memory_presolve_new(
    conjuncts: list[FNode],
    bool_vars: set[FNode],
    *,
    coi_constraints: list[FNode],
    interactions: list[Any],
    match_vars: dict[tuple[int, int], FNode],
) -> list[FNode]:
    """Like :func:`plain_memory_presolve`, but COI and solver checks are per literal.

    For each remaining match variable ``v`` at indices ``(i, j)``, include the full
    timestamp COI of ``coi_constraints``, a one-step COI of the working
    conjuncts around ``v``, then check validity.
    """
    var_to_indices = {v: ij for ij, v in match_vars.items()}
    log_prefix = "plain_memory_presolve_new"
    t0 = time.monotonic()
    n_tracked0 = len(bool_vars)
    working = list(conjuncts)
    units: dict[FNode, bool] = {}
    pending = list(bool_vars)
    idx = 0
    iterations = 0

    def try_imply_unit(v: FNode) -> FNode | None:
        formula = coi_for_match_imply(
            coi_constraints,
            working,
            interactions,
            var_to_indices[v],
            v,
        )
        return _fresh_is_valid(formula, [Not(v), v], log_prefix=log_prefix)

    def apply_propagation() -> None:
        working[:] = boolean_propagate(working)
        _record_new_unit_prefix(working, units)
        bool_vars.difference_update(_top_level_fixed_bool_symbols(working))

    apply_propagation()
    idx = 0

    while True:
        iterations += 1
        found = False
        start_idx = idx

        while idx < len(pending):
            v = pending[idx]
            idx += 1
            if v not in bool_vars:
                continue
            new_lit = try_imply_unit(v)
            if new_lit is None:
                continue
            k = _unit_bool_key(new_lit)
            if k is not None:
                sym, pol = k
                if sym not in units:
                    units[sym] = pol
                    logging.debug(
                        "%s: solver implied unit %s", log_prefix, new_lit
                    )
            working.insert(0, new_lit)
            apply_propagation()
            found = True
            break

        logging.debug(
            "%s round %d: todo=%d idx=%d/%d found=%s",
            log_prefix,
            iterations,
            len(bool_vars),
            idx,
            len(pending),
            found,
        )
        idx = idx % len(pending)
        if not found and start_idx == 0:
            break

    out = [(sym if pol else Not(sym)).simplify() for sym, pol in units.items()]
    elapsed_ms = (time.monotonic() - t0) * 1000.0
    n_tracked1 = len(bool_vars)
    remaining = ", ".join(sorted(str(v) for v in bool_vars))
    logging.debug(
        "%s: %.1f ms, %d rounds, tracked match_vars %d -> %d "
        "(%d fixed / dropped), %d learned unit literals for output; "
        "remaining unknown match_vars (%d): %s",
        log_prefix,
        elapsed_ms,
        iterations,
        n_tracked0,
        n_tracked1,
        n_tracked0 - n_tracked1,
        len(out),
        n_tracked1,
        remaining if remaining else "(none)",
    )
    return out
