"""Negation normal form conversion for PySMT formulas via a custom substituter."""
from ..smt.utils import *


class NNFConverter(substituter.Substituter):
    """Push negations inward (``Implies``, ``Iff``, quantifiers) toward literal-literal NNF."""

    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    def _again(self, f):
        """Re-run NNF conversion once (used after structural changes)."""
        return type(self)(self.env).substitute(f)

    def walk_implies(self, formula, args, **kwargs):
        """``a => b`` → ``Or(Not(a), b)`` then recurse."""
        return self._again(self.mgr.Or(self.mgr.Not(args[0]), args[1]))

    def walk_not(self, formula, args, **kwargs):
        """Push negation through ``Not``, ``Ite``, ``And``, ``Or``."""
        arg = args[0]
        if arg.is_not():
            return arg.arg(0)
        if arg.is_ite():
            return self.mgr.Not(arg)
        if arg.is_and():
            return self._again(self.mgr.Or([self.mgr.Not(a) for a in arg.args()]))
        if arg.is_or():
            return self._again(self.mgr.And([self.mgr.Not(a) for a in arg.args()]))
        return self.mgr.Not(arg)

    def walk_and(self, formula, args, **kwargs):
        """Flatten nested ``And`` while rebuilding in NNF."""
        flat = []
        for a in args:
            if a.is_and():
                flat.extend(a.args())
            else:
                flat.append(a)
        match flat:
            case []:
                return self.mgr.TRUE()
            case [a]:
                return a
            case lst:
                return self.mgr.And(lst)

    def walk_or(self, formula, args, **kwargs):
        """Flatten nested ``Or`` while rebuilding in NNF."""
        flat = []
        for a in args:
            if a.is_or():
                flat.extend(a.args())
            else:
                flat.append(a)
        match flat:
            case []:
                return self.mgr.FALSE()
            case [a]:
                return a
            case lst:
                return self.mgr.Or(lst)


def simplify_nnf(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run ``NNFConverter`` on every asserted formula in the script."""
    conv = NNFConverter()
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = conv.substitute(cmd.args[0])
    return smt_script
