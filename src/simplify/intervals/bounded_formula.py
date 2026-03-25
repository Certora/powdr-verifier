from __future__ import annotations

from dataclasses import dataclass

from ...smt.utils import *
from .domain import IntDomain, IntVarDomains
from .reasoner import IntervalReasoner


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
        conjoined with the rebuilt conjuncts. ``ForAll`` / ``Exists`` are rebuilt with the
        original quantifier variables; other boolean operators use ``create_node``.
        Non-boolean nodes are returned as-is (they have no children).
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

    def refine_domains(self, context: frozenset[FNode] = frozenset()) -> bool:
        """Intersect ``domains`` with information implied by ``formula`` and ``context``.

        Refinement runs ``IntervalReasoner._refine_atom`` on every formula in ``context``,
        and on ``formula`` when it is not a boolean operator (``is_bool_op()``), in fixpoint
        rounds (up to 8). If there is nothing to refine (``formula`` is a boolean operator
        and ``context`` is empty), returns ``False``. Returns ``True`` iff ``domains``
        changed.
        """
        atoms: list[FNode] = list(context)
        if not self.formula.is_bool_op():
            if self.formula not in context:
                atoms.append(self.formula)
        if not atoms:
            return False
        r = IntervalReasoner()
        base: dict[FNode, IntDomain] = dict(self.domains.to_dict())
        for _ in range(8):
            cache: dict[FNode, IntDomain] = {}
            changed = False
            for atom in atoms:
                changed |= r._refine_atom(
                    atom,
                    base,
                    cache,
                    formula_ctx="BoundedFormula.refine_domains",
                )
            if not changed or r._state_inconsistent(base):
                break
        old_domains = self.domains
        self.domains = IntVarDomains.from_mapping(base)
        return self.domains != old_domains

    def push_down(self) -> bool:
        """Narrow each child's ``domains`` by intersecting with this node's ``domains``.

        Non-boolean leaves have no ``subformulas``, so this is a no-op there. Returns
        ``True`` if any child map changed.
        """
        progress = False
        for sub in self.subformulas:
            merged = sub.domains.intersect(self.domains)
            if merged != sub.domains:
                progress = True
            sub.domains = merged
        return progress

    def lift_up(self) -> bool:
        """Lift children's ``domains`` into this node, then meet with ``self.domains``.

        ``And`` folds with ``top`` and ``intersect``; ``Or`` with ``bottom`` and ``union``
        (hull semantics per ``domain.py``). Other boolean operators are unchanged (returns
        ``False``). No children → no-op.
        """
        if not self.subformulas:
            return False
        if self.formula.is_and():
            lifted = IntVarDomains.top()
            for sub in self.subformulas:
                lifted = lifted.intersect(sub.domains)
        elif self.formula.is_or():
            lifted = IntVarDomains.bottom()
            for sub in self.subformulas:
                lifted = lifted.union(sub.domains)
        else:
            return False
        old_domains = self.domains
        self.domains = old_domains.intersect(lifted)
        return self.domains != old_domains

    def refine_recursive(self, context: frozenset[FNode] = frozenset()) -> bool:
        """Refine ``domains`` over this subtree (children first, then lift).

        ``context`` collects conjunctive constraints from enclosing ``And`` nodes: when
        ``formula`` is a conjunction, each direct child whose ``formula`` is not a
        boolean operator (``is_bool_op()``) is added, then the same frozenset is passed to
        recursive calls. Defaults to an empty frozenset.

        Leaves without ``subformulas`` call ``refine_domains`` with that context.
        Otherwise, repeat ``push_down``, recursive refinement of each child, then
        ``lift_up`` until ``domains`` is bottom or a full round makes no progress.
        Returns ``True`` if any refinement step changed a domain map in this subtree.
        """
        if self.formula.is_and():
            ctx = context | frozenset(
                sub.formula for sub in self.subformulas if not sub.formula.is_bool_op()
            )
        else:
            ctx = context
        progress_any = self.refine_domains(ctx)
        if not self.subformulas:
            return progress_any
        while not self.domains.is_bottom():
            progress = False
            if self.push_down():
                progress = True
            for sub in self.subformulas:
                if sub.refine_recursive(ctx):
                    progress = True
            if self.lift_up():
                progress = True
            if not progress:
                break
            progress_any = True
        return progress_any
