"""Lift PySMT formulas to interval-aware ``BoundedFormula`` views for analysis."""
from __future__ import annotations

import logging
from dataclasses import dataclass

from ...smt.utils import *
from .domain import IntDomain, IntVarDomains
from .reasoner import IntervalReasoner

logger = logging.getLogger(__name__)


def _fmt_formula(f: FNode, max_len: int = 200) -> str:
    """Truncate ``str(f)`` for debug logs."""
    s = str(f)
    if len(s) <= max_len:
        return s
    return s[: max_len - 3] + "..."


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
        """Build leaf or boolean-op tree with ``IntVarDomains.top()``."""
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
            vars = self.formula.get_free_variables()
            bounds = [b for b in self.domains.to_constraints(vars) if b not in children]
            return And(
                *children,
                *bounds,
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
        if self.domains.is_bottom():
            return False
        atoms: list[FNode] = list(context)
        if not self.formula.is_bool_op():
            if self.formula not in context:
                atoms.append(self.formula)
        if not atoms:
            logger.debug("refine_domains: skip (no atoms) %s", _fmt_formula(self.formula))
            return False
        r = IntervalReasoner()
        base: dict[FNode, IntDomain] = dict(self.domains.to_dict())
        for _ in range(8):
            changed = False
            for atom in atoms:
                #logger.debug(f"refine_domains: refining atom {atom}")
                changed |= r._refine_atom(
                    atom,
                    base,
                    formula_ctx="BoundedFormula.refine_domains",
                )
                if r._state_inconsistent(base):
                    logger.debug(f"refine_domains: inconsistent after refining atom {atom}")
                    break
            if not changed or r._state_inconsistent(base):
                break
        old_domains = self.domains
        self.domains = IntVarDomains.from_mapping(base)
        changed = self.domains != old_domains
        if changed:
            logger.debug("refine_domains: domains changed %s", _fmt_formula(self.formula))
        return changed

    def push_down(self) -> bool:
        """Narrow each child's ``domains`` by intersecting with this node's ``domains``.

        Non-boolean leaves have no ``subformulas``, so this is a no-op there. Returns
        ``True`` if any child map changed.
        """
        progress = False
        for sub in self.subformulas:
            merged = sub.domains.intersect(self.domains)
            if merged != sub.domains:
                logger.debug("push_down: narrowed child %s to %s", _fmt_formula(sub.formula), merged)
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
        changed = self.domains != old_domains
        if changed:
            logger.debug("lift_up: domains changed under %s", _fmt_formula(self.formula))
        return changed

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
        if progress_any:
            logger.debug(
                "refine_domain: leaf progressed bottom=%s %s",
                self.domains.is_bottom(),
                _fmt_formula(self.formula),
            )
        if not self.subformulas:
            if progress_any:
                logger.debug(
                    "refine_recursive: leaf progressed bottom=%s %s",
                    self.domains.is_bottom(),
                    _fmt_formula(self.formula),
                )
            return progress_any
        round_no = 0
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
                logger.debug(
                    "refine_recursive: fixpoint after %d round(s) %s",
                    round_no,
                    _fmt_formula(self.formula),
                )
                break
            progress_any = True
            round_no += 1
            logger.debug(
                "refine_recursive: round %d progressed under %s",
                round_no,
                _fmt_formula(self.formula),
            )
        if self.domains.is_bottom():
            logger.debug("refine_recursive: bottom domain %s", _fmt_formula(self.formula))
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug(
                "refine_recursive: subtree done progress=%s bottom=%s %s",
                progress_any,
                self.domains.is_bottom(),
                _fmt_formula(self.formula),
            )
        return progress_any

    def simplify(self, domains: IntVarDomains[FNode], context: frozenset[FNode]) -> None:
        """Refine ``domains`` from ``context``, simplify children, then recurse.

        Order: assign ``domains`` and call ``refine_domains(context)`` (only the given
        context, not sibling conjuncts). Then evaluate each direct subformula on the
        refined store and replace with ``Bool(True)`` / ``Bool(False)`` when definite.
        Intersect each child's domains with this node's (``push_down``). If this node is
        a conjunction, extend ``context`` with direct non-operator children; pass that
        to recursive ``simplify`` on each child.
        """
        if not self.subformulas:
            return
        self.domains = domains
        self.refine_domains(context)

        r = IntervalReasoner()
        state: dict[FNode, IntDomain] = dict(self.domains.to_dict())
        for sub in self.subformulas:
            vb = r._eval_bool(sub.formula, state)
            if vb is True:
                sub.formula = Bool(True)
                sub.subformulas = []
            elif vb is False:
                sub.formula = Bool(False)
                sub.subformulas = []

        child_ctx = context
        if self.formula.is_and():
            child_ctx = child_ctx | frozenset(
                sub.formula for sub in self.subformulas if not sub.formula.is_bool_op()
            )
        for sub in self.subformulas:
            sub.simplify(domains, child_ctx)
