from ..smt.utils import *

class ModUnroller(substituter.Substituter):
    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    @substituter.handles(
        set(operators.ALL_TYPES) - frozenset([operators.MOD])
    )
    def walk_identity(self, formula, args, **kwargs):
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.MOD]))
    def walk_unroll_mod(self, formula, args, **kwargs):
        l,r = args
        return Ite(
            And(LE(Int(0), l), LT(l, r)),
            l,
            Mod(l, r)
        )

def unroll_mod(formula: FNode) -> FNode:
    return ModUnroller().substitute(formula)
