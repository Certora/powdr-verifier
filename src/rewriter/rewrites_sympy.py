from sympy import *

from ..utils.args import ARGS

from ..utils.profiling import simple_profile
from .utils import unpack_modeq

### This is sympy land! Do not use pysmt here!


def normalize(e: Expr) -> Expr:
    """Expand and reduce `e` modulo the configured field modulus."""
    return expand(e, modulus=ARGS().field_type.value)


@simple_profile
def rewrite_choice(node: Expr) -> Expr:
    """Rewrite `Mod(f1*...*fn, p) == 0` into a disjunction of `Mod(fi, p) == 0` (best-effort)."""
    match unpack_modeq(node):
        case e, c:
            factors = factor(e)
            if isinstance(factors, Mul):
                factors = list(factors.args)
                if len(factors) > 1:
                    return Or(*[Eq(Mod(normalize(f), c), 0) for f in factors])
    return None


@simple_profile
def rewrite_mod_equality(node: Expr) -> Expr:
    """Rewrite simple modular equalities like `s - c == 0 (mod p)` into `s == c mod p`."""
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
            if m := expr.match(s + (ARGS().field_type.value - 1) * s2):
                return Eq(m[s], m[s2])
            if m := expr.match(c + (ARGS().field_type.value - 1) * s):
                return Eq(m[s], m[c])
    return None
