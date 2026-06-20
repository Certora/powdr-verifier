"""SymPy-only rewrites for modular equalities (no PySMT imports in rule bodies)."""
import functools

from sympy import *

from ..utils.args import ARGS

from ..utils.profiling import simple_profile
from .utils import unpack_modeq

### This is sympy land! Do not use pysmt here!


def normalize(e: Expr) -> Expr:
    """Expand and reduce `e` modulo the configured field modulus."""
    return expand(e, modulus=ARGS().field_type.value)


def _solved_roots(factors: list, p: int):
    """``(x, roots)`` when every factor is linear in one symbol (Pow allowed)."""
    p = int(p)
    x = None
    values: set = set()
    for f in factors:
        if f.is_Pow and f.exp.is_Integer and f.exp > 0:
            f = f.base
        if f.is_Integer:
            if int(f) % p == 0:
                return None
            continue
        if not f.free_symbols or len(f.free_symbols) != 1:
            return None
        sym = next(iter(f.free_symbols))
        poly = f.as_poly(sym)
        if poly is None or poly.degree() != 1:
            return None
        if x is None:
            x = sym
        elif x != sym:
            return None
        a, b = (int(v) for v in poly.all_coeffs())
        if a % p == 0:
            return None
        values.add((-b * pow(a, -1, p)) % p)
    if x is None or not values:
        return None
    return x, values


@functools.lru_cache(maxsize=None)
@simple_profile
def rewrite_choice(node: Expr) -> Expr:
    """Rewrite `Mod(f1*...*fn, p) == 0` into a disjunction of `Mod(fi, p) == 0` (best-effort).

    Memoized on the SymPy ``node``: the rule is a pure function of the node and
    the (run-constant) field modulus, and its ``factor()`` call is the most
    expensive single step in the rewriter. With ``to_sympy`` memoized, identical
    equalities reach this rule as the *same* SymPy object, so cross-assert
    duplicates collapse to one ``factor()``.

    When every factor is linear in the same single symbol, the
    congruences are solved to root equalities with the implied interval
    attached (ranges in addition to the disjunction), mirroring
    ``rewrite_choice_simple``.
    """
    match unpack_modeq(node):
        case e, c:
            assert isprime(c), c
            factors = factor(e)
            if isinstance(factors, Mul):
                factors = list(factors.args)
                if len(factors) > 1:
                    solved = _solved_roots(factors, c)
                    if solved is not None:
                        x, values = solved
                        return And(
                            Or(*[Eq(x, Integer(v)) for v in sorted(values)]),
                            Le(Integer(min(values)), x),
                            Le(x, Integer(max(values))),
                        )
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
