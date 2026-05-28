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
    """Pin unpinned int/bool qvars discovered by isolation probes on the forall body.

    Soundness invariant (matching the pre-refactor ``isolate.py``): a qvar
    is only considered when every disjunct mentioning it has ``qvar`` as
    its *only* free variable — neither other qvars nor outer free vars.
    Under that precondition the q-mentioning disjuncts are pure functions
    of ``qvar``, so any value falsifying them all is a uniform witness
    across every assignment of the rest of the formula. Pinning to such a
    witness preserves unsat:

        F unsat means ∀x, other_q. ∃q. ¬⋁_i D_i(q) ∧ ¬E(other_q, x).

    Since the ``D_i`` only depend on ``q``, the existential ``∃q. ¬⋁_i
    D_i(q)`` decouples from ``other_q, x``, and any specific witness
    ``w`` for it works uniformly. Pinning ``q := w`` does not lose unsat.

    The relaxations that have been tried (and undone here):

    * Allowing outer free variables in q-mentioning disjuncts is unsound:
      the ``D_i`` then become ``D_i(q, x)``, the "bad q" depends on ``x``,
      and the probe's one-shot model gives a witness valid only for the
      specific ``x*`` the solver picked.

    * Allowing *other qvars* in q-mentioning disjuncts is similarly
      unsound: a disjunct ``D(q, other_q)`` couples ``q`` to ``other_q``;
      pinning ``q := v_q`` from a model that picks ``other_q = w_o`` only
      establishes the body at ``(v_q, w_o)``, not at ``(v_q, w_o')`` for
      the ``w_o'`` that other constraints elsewhere in the formula force
      on ``other_q``. Verified empirically: an "other-qvars-OK" version
      pinned ``after-memory-N-isinput := False`` on
      ``apc_candidate_2099512_031_low_degree_bus-…_032_inlining.
      completeness`` (via the ``(= isinput (not hadinput-2))`` disjunct
      that mentions both qvars) even though the rest of the formula
      forced ``hadinput-2 = False`` and hence ``isinput = True``,
      producing spurious sat.

    See ``test_isolate_does_not_pin_with_outer_free_var`` and
    ``test_isolate_does_not_pin_with_other_qvar_in_disjunct``.
    """
    if not body.is_or():
        return
    qvars = skolem_map.qvars
    for qvar in qvars:
        qt = qvar.get_type()
        if not (qt.is_int_type() or qt.is_bool_type()):
            continue
        if skolem_map.is_pinned(qvar):
            continue
        containing = [d for d in body.args() if qvar in d.get_free_variables()]
        if not containing:
            continue
        # Strict soundness gate (matches old isolate.py): every q-mentioning
        # disjunct must mention qvar AND NOTHING ELSE.
        if any(d.get_free_variables() - {qvar} for d in containing):
            continue
        falsify_parts = [Not(d) for d in containing]
        value = _find_isolated_value(qvar, qvars, falsify_parts)
        if value is not None:
            skolem_map.pin(qvar, value, source="isolate")
