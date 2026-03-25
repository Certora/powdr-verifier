from __future__ import annotations

from dataclasses import dataclass

from ...smt.utils import *
from .domain import IntVarDomains


@dataclass(slots=True, init=False)
class BoundedFormula:
    """A formula with per-variable integer interval bounds and child nodes.

    Each node carries a pySMT ``FNode``, an ``IntVarDomains`` map (initially top),
    and ``BoundedFormula`` children only under pySMT boolean operators
    (``FNode.is_bool_op()``), recursively unpacking ``formula.args()``. Other
    nodes (e.g. ``Equals``, constants, ``Ite``) are leaves. No DAG bookkeeping.
    """

    formula: FNode
    domains: IntVarDomains[FNode]
    subformulas: list[BoundedFormula]

    def __init__(self, formula: FNode) -> None:
        self.formula = formula
        self.domains = IntVarDomains.top()
        self.subformulas = (
            [BoundedFormula(a) for a in formula.args()] if formula.is_bool_op() else []
        )

    def as_fnode(self) -> FNode:
        """Rebuild an ``FNode`` from this tree, threading child ``as_fnode`` results.

        If ``self.formula`` is a conjunction, interval bounds from ``self.domains`` are
        conjoined with the rebuilt conjuncts.         ``ForAll`` / ``Exists`` are rebuilt with the original quantifier variables;
        other boolean operators use ``create_node``. Non-boolean nodes are returned
        as-is (they have no children).
        """
        if not self.formula.is_bool_op():
            return self.formula
        children = [s.as_fnode() for s in self.subformulas]
        if len(children) != len(self.formula.args()):
            raise ValueError("subformula count does not match formula.args()")
        if not children:
            return self.formula
        if self.formula.is_and():
            return And(
                *children,
                *list(self.domains.to_constraints()),
            )
        if self.formula.is_forall():
            return ForAll(self.formula.quantifier_vars(), children[0])
        if self.formula.is_exists():
            return Exists(self.formula.quantifier_vars(), children[0])
        mgr = get_env().formula_manager
        return mgr.create_node(node_type=self.formula.node_type(), args=tuple(children))
