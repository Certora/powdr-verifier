"""Helpers for the plain (busat-style) memory permutation encoding.

``cone_of_influence`` narrows main constraints to those touching seed variables.
``plain_memory_const_key_io_hints`` adds first/last-occurrence input/output pins
for constant (address_space, pointer) keys. ``plain_memory_presolve_incremental`` alternates boolean unit propagation and
incremental SMT checks: full timestamp COI from ``coi_constraints`` in the solver base,
then per match variable a pushed one-step COI from the conjuncts before checking polarities.
``plain_memory_presolve_individual`` does the same but uses a fresh solver per literal, with
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
    seen: set[FNode] = set()

    def record_literal(lit: FNode, round_subs: dict[FNode, FNode]) -> bool:
        if lit.is_symbol(BOOL):
            sym, val = lit, TRUE()
        elif lit.is_not() and lit.arg(0).is_symbol(BOOL):
            sym, val = lit.arg(0), FALSE()
        else:
            return False
        if sym in seen:
            return False
        seen.add(sym)
        round_subs[sym] = val
        literals.append(lit)
        return True

    while True:
        next_remaining: list[FNode] = []
        # Only the bindings discovered this round need to be substituted:
        # everything in ``remaining`` already had all earlier-round bindings
        # applied by the previous iteration's substitute(). Passing the full
        # accumulated dict here is pure waste -- pysmt's substitute() validates
        # every entry in ``subs`` on every call (O(|subs|) per conjunct), which
        # is quadratic in the number of bool units.
        round_subs: dict[FNode, FNode] = {}
        for f in remaining:
            f = keep_comment(f.simplify(), f)
            if record_literal(f, round_subs):
                pass
            elif not f.is_true():
                next_remaining.append(f)
        if not round_subs:
            remaining = next_remaining
            break
        remaining = [keep_comment(substitute_no_validate(g, round_subs), g) for g in next_remaining]

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


def _all_timestamp_vars(interactions: list[Any]) -> set[FNode]:
    ts_vars: set[FNode] = set()
    for bi in interactions:
        if bi.args:
            ts_vars |= bi.args[-1].get_free_variables()
    return ts_vars


def _first_valid_literal(
    solver: Solver,
    literals: list[FNode],
    *,
    log_prefix: str,
) -> FNode | None:
    """Return the first literal entailed at the current solver scope, if any."""
    for lit in literals:
        solver.push()
        solver.add_assertion(Not(lit))
        try:
            if not solver.solve():
                return lit
        except SolverReturnedUnknownResultError:
            logging.info("%s: is_valid unknown for %s", log_prefix, lit)
        except Exception:
            logging.info("%s: is_valid failed for %s", log_prefix, lit)
        finally:
            solver.pop()
    return None


def _fresh_is_valid(
    conjuncts: list[FNode],
    literals: list[FNode],
    *,
    log_prefix: str,
    timeout: int,
) -> FNode | None:
    """Return the first literal in ``literals`` entailed by ``conjuncts``, if any."""
    if not literals:
        return None
    try:
        with Solver(
            logic=logics.ALL,
            name="z3",
            incremental=True
        ) as s:
            s.z3.set("timeout", timeout)
            for c in conjuncts:
                s.add_assertion(c)
            return _first_valid_literal(s, literals, log_prefix=log_prefix)
    except Exception:
        logging.info("%s: is_valid failed for %s", log_prefix, literals)
    return None


def _collect_implied_top_level_literals(
    full_ts_coi: list[FNode],
    working: list[FNode],
    bool_vars: set[FNode],
    *,
    log_prefix: str,
    timeout: int,
) -> list[FNode]:
    """Entailed match literals via incremental checks with layered COI."""
    if not bool_vars:
        return []
    out: list[FNode] = []
    with Solver(
        logic=logics.ALL,
        name="z3",
        incremental=True,
        solver_options={"rlimit": 10000000},
    ) as s:
        s.z3.set("timeout", timeout)
        for c in full_ts_coi:
            s.add_assertion(c)
        for v in list(bool_vars):
            s.push()
            for c in cone_of_influence_one_step(working, {v}):
                s.add_assertion(c)
            lit = _first_valid_literal(s, [Not(v), v], log_prefix=log_prefix)
            s.pop()
            if lit is None:
                continue
            out.append(lit)
            logging.info("%s: solver implied unit %s", log_prefix, lit)
            s.add_assertion(lit)
    return out


def plain_memory_presolve_incremental(
    conjuncts: list[FNode],
    bool_vars: set[FNode],
    *,
    coi_constraints: list[FNode],
    interactions: list[Any],
    match_vars: dict[tuple[int, int], FNode],
) -> list[FNode]:
    """Learn unit bool facts for match variables; mutates ``bool_vars`` in place."""
    _ = match_vars
    log_prefix = "plain_memory_presolve_incremental"
    full_ts_coi = cone_of_influence(
        coi_constraints, _all_timestamp_vars(interactions)
    )
    t0 = time.monotonic()
    n_tracked0 = len(bool_vars)
    n_coi = len(coi_constraints)
    working = list(conjuncts)
    units: dict[FNode, bool] = {}
    iterations = 0
    timeout = max(25, 1000 // max(len(bool_vars), 1))
    while len(bool_vars) > 0:
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

        new_lits = _collect_implied_top_level_literals(
            full_ts_coi,
            working,
            bool_vars,
            log_prefix=log_prefix,
            timeout=timeout,
        )
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
            "plain_memory_presolve_incremental round %d: tracked=%d implied_lits=%d changed=%s",
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
        "plain_memory_presolve_incremental: %.1f ms, %d rounds, tracked match_vars %d -> %d "
        "(%d fixed / dropped), %d learned unit literals for output, %d coi conjuncts; "
        "remaining unknown match_vars (%d): %s",
        elapsed_ms,
        iterations,
        n_tracked0,
        n_tracked1,
        n_tracked0 - n_tracked1,
        len(out),
        n_coi,
        n_tracked1,
        remaining if remaining else "(none)",
    )
    return out


def plain_memory_presolve_individual(
    conjuncts: list[FNode],
    bool_vars: set[FNode],
    *,
    coi_constraints: list[FNode],
    interactions: list[Any],
    match_vars: dict[tuple[int, int], FNode],
) -> list[FNode]:
    """Like :func:`plain_memory_presolve_incremental`, but COI and solver checks are per literal.

    For each remaining match variable ``v`` at indices ``(i, j)``, include the full
    timestamp COI of ``coi_constraints``, a one-step COI of the working
    conjuncts around ``v``, then check validity.
    """
    var_to_indices = {v: ij for ij, v in match_vars.items()}
    log_prefix = "plain_memory_presolve_individual"
    t0 = time.monotonic()
    n_tracked0 = len(bool_vars)
    working = list(conjuncts)
    units: dict[FNode, bool] = {}
    pending = list(bool_vars)
    idx = 0
    iterations = 0
    timeout = 1000 // len(bool_vars)

    def try_imply_unit(v: FNode) -> FNode | None:
        formula = coi_for_match_imply(
            coi_constraints,
            working,
            interactions,
            var_to_indices[v],
            v,
        )
        return _fresh_is_valid(formula, [Not(v), v], log_prefix=log_prefix, timeout=timeout)

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
                    logging.info(
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
