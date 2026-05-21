"""Substitute solver model values into assertions (definition forms per sort)."""
import logging

from ..smt.utils import *


def _definition_for(var: FNode, value: FNode) -> FNode:
    """``Iff`` for bools, ``Equals`` otherwise (definition of ``var`` from model value)."""
    if var.get_type().is_bool_type():
        return Iff(var, value)
    return Equals(var, value)


def _model_value(model, var: FNode) -> FNode | None:
    """Look up ``var`` in a PySMT model mapping; ``None`` if absent."""
    for k, v in model:
        if k == var:
            return v
    return None


def _find_isolated_value(var: FNode, disjuncts: list[FNode]) -> FNode | None:
    """If ``Not(And(disjuncts))`` is unsat, return ``var``'s value in a model; else ``None``."""
    try:
        with Solver(logic=QF_UFNIA, solver_options={"timeout": 500}) as solver:
            solver.add_assertion(And(Not(d) for d in disjuncts))
            if not solver.solve():
                return None
            return _model_value(solver.get_model(), var)
    except Exception as e:
        logging.debug(f"failed isolated-variable check for {var}: {e}")
        return None


class IsolateWalker(IdentityDagWalker):
    """Add ``Not(definition)`` disjuncts when a qvar is uniquely determined on a subset of disjuncts."""

    def walk_forall(self, formula, args, **kwargs):
        """For each qvar, if some disjuncts mention only that qvar, negate its forced assignment."""
        body = args[0]
        if not body.is_or():
            return formula

        qvars = frozenset(formula.quantifier_vars())
        new_disjuncts = []
        for qvar in qvars:
            containing = [d for d in body.args() if qvar in d.get_free_variables()]
            if not containing:
                continue
            if any(d.get_free_variables() - {qvar} for d in containing):
                continue
            value = _find_isolated_value(qvar, containing)
            if value is not None:
                new_disjuncts.append(Not(_definition_for(qvar, value)))

        if not new_disjuncts:
            return formula
        return ForAll(formula.quantifier_vars(), Or(*body.args(), *new_disjuncts))


def simplify_isolate(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Strengthen ``forall`` bodies using cheap QF_UFNIA checks for isolated quantified variables."""
    w = IsolateWalker(env=get_env())
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
    return smt_script
