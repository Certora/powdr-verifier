import logging

from .smt_utils import *
from .args import ARGS

def rewrite_mul2or(input: FNode) -> FNode:
    '''(= (uf_mod (* x (- x 1)) C) 0) --> (or (= (uf_mod x C) 0) (= (uf_mod x C) 1))'''
    if not input.is_equals(): return None
    mod, zero = input.args()

    if not mod.is_function_application(): return None
    fname = mod.function_name()
    if not fname.is_symbol(): return None
    if not fname.symbol_name() == UF_MOD.symbol_name(): return None

    if not zero.is_zero(): return None
    times, const = mod.args()
    if not times.is_times(): return None
    if not const.is_int_constant(): return None
    x, sub = times.args()
    if not x.is_symbol(): return None
    if not sub.is_minus(): return None
    x2, one = sub.args()
    if not x2 == x: return None
    if not one.is_one(): return None
    
    return Or(
        Equals(Function(fname, [x, const]), Int(0)),
        Equals(Function(fname, [x, const]), Int(1))
    )

def rewrite_reflexiveeq(input: FNode) -> FNode:
    '''(= x x) --> True'''
    if not input.is_equals(): return None
    left, right = input.args()
    if not left == right: return None
    return TRUE()

def rewrite_reflexiveminus(input: FNode) -> FNode:
    '''(- x x) --> 0'''
    if not input.is_minus(): return None
    left, right = input.args()
    if not left == right: return None
    return Int(0)

def rewrite_minuszero(input: FNode) -> FNode:
    '''(- x 0) --> x'''
    if not input.is_minus(): return None
    left, right = input.args()
    if not right.is_zero(): return None
    return left

REWRITES = {
    operators.EQUALS: [rewrite_mul2or, rewrite_reflexiveeq],
    operators.MINUS: [rewrite_reflexiveminus, rewrite_minuszero],
}

class Rewriter(substituter.Substituter):
    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)
    
    @substituter.handles(set(operators.ALL_TYPES) - operators.QUANTIFIERS)
    def walk_identity_or_replace(self, formula, args, **kwargs):
        for rewrite in REWRITES.get(formula.node_type(), []):
            result = rewrite(formula)
            if result is not None:
                self.did_rewrite = True
                if ARGS().log_rewrites:
                    logging.info(f'rewrote {formula} --> {result}')
                return keep_comment(result, formula)
        return keep_comment(substituter.Substituter.super(self, formula, args=args, **kwargs), formula)

def rewrite(input: FNode) -> FNode:
    rewriter = Rewriter()
    while True:
        rewriter.did_rewrite = False
        input = rewriter.substitute(input)
        if not rewriter.did_rewrite:
            break
    return input
