import sympy

from .conversion import to_sympy, to_smt
from .rewrites import rewrite_choice, rewrite_mod_equality

from ..smt.utils import *

REWRITES = [
    rewrite_choice,
    rewrite_mod_equality,
]
MAX_REWRITE_COUNT = 3

@simple_profile
def rewrite_one(node: sympy.Expr) -> sympy.Expr:
    for r in REWRITES:
        res = r(node)
        if res is not None:
            return res
    return node


class RelationRewriter(substituter.Substituter):
    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)
    
    @substituter.handles(set(operators.ALL_TYPES) - frozenset([operators.EQUALS]))
    def walk_identity(self, formula, args, **kwargs):
        return keep_comment(substituter.Substituter.super(self, formula, args=args, **kwargs), formula)

    @substituter.handles(frozenset([operators.EQUALS]))
    def walk_identity_or_replace(self, formula, args, **kwargs):
        try:
            res = to_smt(rewrite_one(to_sympy(formula)))
        except AssertionError:
            res = formula
        if res != formula:
            if ARGS().log_rewrites:
                logging.info(f"rewrote {formula} --> {res}")
            return keep_comment(res, formula)
        return keep_comment(substituter.Substituter.super(self, formula, args=args, **kwargs), formula)

@simple_profile
def rewrite(input: FNode) -> FNode:
    if isinstance(input, list):
        return [rewrite(i) for i in input]
    relation_rewriter = RelationRewriter()
    last = None
    for _ in range(MAX_REWRITE_COUNT):
        last = input
        input = relation_rewriter.substitute(input)
        if last == input:
            break
    return input
