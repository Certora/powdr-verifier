from ..smt.utils import *

class Andifier(substituter.Substituter):
    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    def walk_or(self, formula, args, **kwargs):
        return Not(And(Not(a) for a in args))

class DoubleNegationRemover(substituter.Substituter):
    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    def walk_not(self, formula, args, **kwargs):
        assert len(args) == 1
        arg = args[0]
        if arg.is_not():
            return arg.arg(0)
        return Not(arg)

def simplify_andify(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    dnr = DoubleNegationRemover()
    andify = Andifier()

    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = dnr.substitute(andify.substitute(cmd.args[0]))
    return smt_script
