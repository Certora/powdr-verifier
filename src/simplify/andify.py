"""SMT pass: push disjunctions under negation toward NNF-style ``And`` of ``Or``."""
from ..smt.utils import *

class Andifier(substituter.Substituter):
    """Rewrite ``Or`` as ``Not(And(Not …))`` to bias formulas toward conjunctions."""

    def __init__(self, env=None):
        """Optional PySMT ``Environment``."""
        substituter.Substituter.__init__(self, env=env)

    def walk_or(self, formula, args, **kwargs):
        """De Morgan: ``Or(a,b,…)`` → ``Not(And(Not(a),…))``."""
        return Not(And(Not(a) for a in args))

class DoubleNegationRemover(substituter.Substituter):
    """Cancel ``Not(Not(x))`` → ``x`` while traversing under the substituter."""

    def __init__(self, env=None):
        """Optional PySMT ``Environment``."""
        substituter.Substituter.__init__(self, env=env)

    def walk_not(self, formula, args, **kwargs):
        """Remove double negation ``Not(Not(x))`` → ``x``."""
        assert len(args) == 1
        arg = args[0]
        if arg.is_not():
            return arg.arg(0)
        return Not(arg)

def simplify_andify(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Apply ``Andifier`` then ``DoubleNegationRemover`` to each asserted formula."""
    dnr = DoubleNegationRemover()
    andify = Andifier()

    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = dnr.substitute(andify.substitute(cmd.args[0]))
    return smt_script
