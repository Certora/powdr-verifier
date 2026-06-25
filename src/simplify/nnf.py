"""Negation normal form conversion for PySMT formulas via a custom substituter."""
from ..smt.utils import *


class NNFConverter(substituter.Substituter):
    """Push negations inward (``Implies``, ``Ite``, ``And``, ``Or``) toward NNF."""

    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    @staticmethod
    def _flatten_and(args: list[FNode]) -> FNode:
        flat: list[FNode] = []
        for a in args:
            if a.is_and():
                flat.extend(a.args())
            else:
                flat.append(a)
        match flat:
            case []:
                return TRUE()
            case [a]:
                return a
            case lst:
                return And(*lst)

    @staticmethod
    def _flatten_or(args: list[FNode]) -> FNode:
        flat: list[FNode] = []
        for a in args:
            if a.is_or():
                flat.extend(a.args())
            else:
                flat.append(a)
        match flat:
            case []:
                return FALSE()
            case [a]:
                return a
            case lst:
                return Or(*lst)

    def _negate(self, formula: FNode) -> FNode:
        """``Not(formula)`` in NNF, assuming ``formula`` is already in NNF."""
        if formula.is_not():
            return formula.arg(0)
        if formula.is_ite():
            return Not(formula)
        if formula.is_and():
            return self._flatten_or([self._negate(a) for a in formula.args()])
        if formula.is_or():
            return self._flatten_and([self._negate(a) for a in formula.args()])
        return Not(formula)

    def walk_implies(self, formula, args, **kwargs):
        """``a => b`` → ``Or(Not(a), b)`` with negation pushed into ``a``."""
        return self._flatten_or([self._negate(args[0]), args[1]])

    def walk_not(self, formula, args, **kwargs):
        """Push negation through ``Not``, ``Ite``, ``And``, ``Or``."""
        return self._negate(args[0])

    def walk_and(self, formula, args, **kwargs):
        """Flatten nested ``And`` while rebuilding in NNF."""
        return self._flatten_and(args)

    def walk_or(self, formula, args, **kwargs):
        """Flatten nested ``Or`` while rebuilding in NNF."""
        return self._flatten_or(args)


def convert_to_nnf(formula: FNode) -> FNode:
    """Convert ``formula`` to negation normal form."""
    return NNFConverter().substitute(formula)


def simplify_nnf(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Run ``NNFConverter`` on every asserted formula in the script."""
    conv = NNFConverter()
    changed = 0
    total = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            total += 1
            old = cmd.args[0]
            new = conv.substitute(old)
            cmd.args[0] = new
            if new != old:
                changed += 1
    if subaction is not None:
        subaction += {"asserts": total, "asserts_changed": changed}
    return smt_script
