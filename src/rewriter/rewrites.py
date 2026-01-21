from sympy import *

from .utils import unpack_modeq

### This is sympy land! Do not use pysmt here!

def rewrite_choice(node: Expr) -> Expr:
    match unpack_modeq(node):
        case e, c:
            factors = factor(e)
            if isinstance(factors, Mul):
                return Or(
                    *[Eq(Mod(f, c), 0) for f in factors.args]
                )
    return None

def rewrite_mod_equality(node: Expr) -> Expr:
    match unpack_modeq(node):
        case expr, modulus:
            s = Wild("s", properties=[lambda k: k.is_Symbol])
            s2 = Wild("s2", properties=[lambda k: k.is_Symbol])
            c = Wild("c", properties=[lambda k: k.is_Integer])
            if m := expr.match(s - c):
                return Eq(m[s], Mod(m[c], modulus))
            if m := expr.match(c - s):
                return Eq(m[s], Mod(m[c], modulus))
            if m := expr.match(s - s2):
                return Eq(m[s], m[s2])
    return None
