"""Isolation skolem contributor (last in the skolem chain).

Field-bounded QF_UFNIA probes pin quantified int/bool variables that are forced
when falsifying relevant ``Or`` limbs. Runs after rules, derived, witness, and
same-name contributors.
"""
import logging

from ..smt.utils import *


def _model_value(model, var: FNode) -> FNode | None:
    """Look up ``var`` in a PySMT model mapping; ``None`` if absent."""
    for k, v in model:
        if k == var:
            return v
    return None


def _extract_polarized(
    node: FNode, negated: bool, qvar: FNode, qvars: frozenset[FNode]
) -> list[tuple[FNode, bool]] | None:
    """Collect (subformula, polarity) atoms mentioning only ``qvar`` among ``qvars``.

    ``polarity`` is False if ``subformula`` must hold (as-is) when ``node`` holds under
    the current negation stack, True if ``Not(subformula)`` must hold.

    Returns ``None`` when decomposition is aborted (unsafe to slice), e.g. ``Not(And(…))``.
    """
    if node.is_not():
        ch = node.arg(0)
        if ch.is_and():
            return None
        return _extract_polarized(ch, not negated, qvar, qvars)
    if node.is_and():
        acc: list[tuple[FNode, bool]] = []
        for c in node.args():
            part = _extract_polarized(c, negated, qvar, qvars)
            if part is None:
                return None
            acc.extend(part)
        return acc
    if node.is_or():
        if qvar not in node.get_free_variables():
            return []
        fv_q = node.get_free_variables() & qvars
        if fv_q - {qvar}:
            return None
        return [(node, negated)]
    if qvar not in node.get_free_variables():
        return []
    fv_q = node.get_free_variables() & qvars
    if fv_q - {qvar}:
        return None
    return [(node, negated)]


def _must_hold_when_disjunct_holds(phi: FNode, negated: bool) -> FNode:
    return Not(phi) if negated else phi


def _implied_cube_for_disjunct(
    disj: FNode, qvar: FNode, qvars: frozenset[FNode]
) -> FNode | None:
    """Return ``cube`` with ``disj => cube`` (only ``qvar`` among ``qvars`` in ``cube``), or ``None``."""
    ext = _extract_polarized(disj, False, qvar, qvars)
    if ext is None or not ext:
        return None
    parts = [_must_hold_when_disjunct_holds(p, n) for p, n in ext]
    return parts[0] if len(parts) == 1 else And(*parts)


def _falsify_replacement(disj: FNode, qvar: FNode, qvars: frozenset[FNode]) -> FNode | None:
    """Formula ``F`` with ``F => Not(disj)`` (strong enough to use instead of ``Not(disj)`` in probes)."""
    cube = _implied_cube_for_disjunct(disj, qvar, qvars)
    if cube is not None:
        return Not(cube)
    fv = disj.get_free_variables()
    if qvar not in fv:
        return None
    if (fv & qvars) - {qvar}:
        return None
    return Not(disj)


def _field_bounds_for_int_qvars(
    falsify_parts: list[FNode], qvars: frozenset[FNode]
) -> list[FNode]:
    """Range axioms ``0 <= v < p`` for int quantified vars that occur in the probe."""
    if not falsify_parts:
        return []
    core = And(*falsify_parts) if len(falsify_parts) > 1 else falsify_parts[0]
    out: list[FNode] = []
    for v in core.get_free_variables():
        if v in qvars and v.get_type().is_int_type():
            out.append(field_symbol(v))
    return out


def _find_isolated_value(
    var: FNode, qvars: frozenset[FNode], falsify_parts: list[FNode]
) -> FNode | None:
    """If probe formula is sat under field bounds on int qvars, return ``var``'s value; else ``None``."""
    try:
        with Solver(logic=QF_UFNIA, solver_options={"timeout": 500}) as solver:
            for ax in _field_bounds_for_int_qvars(falsify_parts, qvars):
                solver.add_assertion(ax)
            probe = And(*falsify_parts) if len(falsify_parts) > 1 else falsify_parts[0]
            solver.add_assertion(probe)
            if not solver.solve():
                return None
            return _model_value(solver.get_model(), var)
    except Exception as e:
        logging.debug(f"failed isolated-variable check for {var}: {e}")
        return None


def contribute(skolem_map, body: FNode) -> None:
    """Pin unpinned int/bool qvars discovered by isolation probes on the forall body."""
    if not body.is_or():
        return
    qvars = skolem_map.qvars
    for qvar in qvars:
        qt = qvar.get_type()
        if not (qt.is_int_type() or qt.is_bool_type()):
            continue
        if skolem_map.is_pinned(qvar):
            continue
        falsify_parts: list[FNode] = []
        for d in body.args():
            if qvar not in d.get_free_variables():
                continue
            rep = _falsify_replacement(d, qvar, qvars)
            if rep is not None:
                falsify_parts.append(rep)
        if not falsify_parts:
            continue
        value = _find_isolated_value(qvar, qvars, falsify_parts)
        if value is not None:
            skolem_map.pin(qvar, value, source="isolate")
