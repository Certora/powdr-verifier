from __future__ import annotations

from dataclasses import dataclass

from ...smt.utils import *
from .domain import IntVarDomains


@dataclass(slots=True, init=False)
class BoundedFormula:
    """A formula with per-variable integer interval bounds and child nodes.

    Each node carries a pySMT ``FNode``, an ``IntVarDomains`` map (initially top),
    and ``BoundedFormula`` children mirroring ``formula.args()``. This is a plain
    tree: no DAG bookkeeping or structural sharing.
    """

    formula: FNode
    domains: IntVarDomains[FNode]
    subformulas: list[BoundedFormula]

    def __init__(self, formula: FNode) -> None:
        self.formula = formula
        self.domains = IntVarDomains.top()
        self.subformulas = [BoundedFormula(a) for a in formula.args()]

    def as_fnode(self) -> FNode:
        """Rebuild an ``FNode`` from this tree, threading child ``as_fnode`` results.

        If ``self.formula`` is a conjunction, interval bounds from ``self.domains`` are
        conjoined with the rebuilt conjuncts. Other node kinds are rebuilt by preserving
        ``node_type`` and swapping in rebuilt arguments.
        """
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
        mgr = get_env().formula_manager
        return mgr.create_node(node_type=self.formula.node_type(), args=tuple(children))
