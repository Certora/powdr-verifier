"""PySMT-side rewrite rules for equalities and modular products (field arithmetic)."""
import logging
from sympy import isprime

from ..utils.args import ARGS
from ..smt.utils import *


def _flatten_times_factors(expr: FNode) -> list[FNode] | None:
    """If `expr` is a (possibly nested) product, return its leaf factors; else None.
    Returns None when there are fewer than two factors."""
    if not expr.is_times():
        return None
    factors: list[FNode] = []

    def collect(n: FNode) -> None:
        if n.is_times():
            for a in n.args():
                collect(a)
        else:
            factors.append(n)

    collect(expr)
    return factors if len(factors) >= 2 else None


def is_mul_by_minus_one(node: FNode) -> Optional[FNode]:
    if node.is_times() and len(node.args()) == 2:
        a, b = node.args()
        if a.is_int_constant(-1) or a.is_int_constant(ARGS().field_type.value - 1):
            return b
        if b.is_int_constant(-1) or b.is_int_constant(ARGS().field_type.value - 1):
            return a
    return None


def _mod_sqrt(n: int, p: int) -> Optional[int]:
    """Modular square root of ``n`` mod prime ``p``, or ``None`` if none exists."""
    n %= p
    if n == 0:
        return 0
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q = p - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m = s
    c = pow(z, q, p)
    t = pow(n, q, p)
    r = pow(n, (q + 1) // 2, p)
    while t != 1:
        i = 1
        t2 = (t * t) % p
        while t2 != 1:
            t2 = (t2 * t2) % p
            i += 1
            if i == m:
                return None
        b = pow(c, 1 << (m - i - 1), p)
        m = i
        c = (b * b) % p
        t = (t * c) % p
        r = (r * b) % p
    return r


def _add_univariate_poly(a: list[int], b: list[int], p: int) -> list[int]:
    n = max(len(a), len(b))
    out = [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    while len(out) > 1 and out[-1] % p == 0:
        out.pop()
    return [c % p for c in out]


def _mul_univariate_poly(
    a: list[int], b: list[int], p: int, max_deg: int
) -> Optional[list[int]]:
    if not a or not b:
        return [0]
    deg = len(a) + len(b) - 2
    if deg > max_deg:
        return None
    out = [0] * (deg + 1)
    for i, ca in enumerate(a):
        for j, cb in enumerate(b):
            out[i + j] = (out[i + j] + ca * cb) % p
    while len(out) > 1 and out[-1] % p == 0:
        out.pop()
    return out


def _poly_in_var(e: FNode, x: FNode, p: int, max_deg: int = 2) -> Optional[list[int]]:
    """Coeffs ``[c0, c1, …]`` for ``c0 + c1*x + …`` in ``x``, or ``None``."""
    if e.is_int_constant():
        return [int(e.constant_value()) % p]
    if e.is_symbol():
        return [0, 1] if e == x else None
    if e.is_plus():
        acc: list[int] = [0]
        for a in e.args():
            pa = _poly_in_var(a, x, p, max_deg)
            if pa is None:
                return None
            acc = _add_univariate_poly(acc, pa, p)
        return acc
    if e.is_minus():
        if len(e.args()) != 2:
            return None
        pa = _poly_in_var(e.arg(0), x, p, max_deg)
        pb = _poly_in_var(e.arg(1), x, p, max_deg)
        if pa is None or pb is None:
            return None
        return _add_univariate_poly(pa, [(-c) % p for c in pb], p)
    if e.is_times():
        acc = [1]
        for a in e.args():
            pa = _poly_in_var(a, x, p, max_deg)
            if pa is None:
                return None
            acc = _mul_univariate_poly(acc, pa, p, max_deg)
            if acc is None:
                return None
        return acc
    return None


def _quadratic_roots_mod(a: int, b: int, c: int, p: int) -> set[int]:
    """Roots of ``a*x^2 + b*x + c == 0 (mod p)``; empty when none exist."""
    a %= p
    b %= p
    c %= p
    if a == 0:
        return set()
    disc = (b * b - 4 * a * c) % p
    if disc == 0:
        return {(-b * pow(2 * a, -1, p)) % p}
    sqrt_disc = _mod_sqrt(disc, p)
    if sqrt_disc is None:
        return set()
    inv = pow(2 * a, -1, p)
    return {((-b + sqrt_disc) * inv) % p, ((-b - sqrt_disc) * inv) % p}


def _solved_quadratic(expr: FNode, p: int) -> Optional[tuple[FNode, set[int]]]:
    """``(x, roots)`` when ``expr`` is a quadratic univariate polynomial."""
    syms = [v for v in expr.get_free_variables() if v.is_symbol()]
    if len(syms) != 1:
        return None
    x = syms[0]
    coeffs = _poly_in_var(expr, x, p, max_deg=2)
    if coeffs is None or len(coeffs) != 3 or coeffs[2] % p == 0:
        return None
    c0, c1, a = coeffs[0], coeffs[1], coeffs[2]
    return x, _quadratic_roots_mod(a, c1, c0, p)


def _solved_roots(factors: list[FNode], p: int) -> Optional[tuple[FNode, set[int]]]:
    """``(x, roots)`` when every factor is linear in the same single symbol.

    Nonzero constant factors contribute no root; a zero constant factor
    makes the product trivially zero (no information), so bail out.
    """
    x: Optional[FNode] = None
    values: set[int] = set()
    for f in factors:
        lf = linear_form(f)
        if lf is None:
            return None
        terms, const = lf
        terms = {s: a % p for s, a in terms.items() if a % p != 0}
        if not terms:
            if const % p == 0:
                return None
            continue
        if len(terms) != 1:
            return None
        sym, a = next(iter(terms.items()))
        if x is None:
            x = sym
        elif x != sym:
            return None
        values.add((-const * pow(a, -1, p)) % p)
    if x is None or not values:
        return None
    return x, values


def roots_with_range(x: FNode, values: set[int]) -> FNode:
    """``x ∈ {values}`` as a disjunction plus the interval it implies.

    The range conjuncts are logically redundant (implied by the
    disjunction) but hand the solver directly propagatable bounds.
    """
    return And(
        Or(*[Equals(x, Int(v)) for v in sorted(values)]),
        LE(Int(min(values)), x),
        LE(x, Int(max(values))),
    )


def rewrite_choice_simple(node_type: int, args: list[FNode]) -> FNode:
    """Rewrite `Mod(e, p) = 0` with field modulus `p` when `e` is a plain product into a disjunction of factor congruences.

    When every factor is linear in the same single variable, the
    congruences are solved to root equalities and the implied interval
    is attached (e.g. ``cmp (cmp - 1) = 0`` becomes
    ``(cmp = 0 or cmp = 1) and 0 <= cmp <= 1``). Solving congruences to
    canonical representatives follows the same convention as
    ``rewrite_mod_equality`` / ``simplify_bounds``.
    """
    assert node_type == operators.EQUALS
    lhs, rhs = args
    if not lhs.is_mod() or not rhs.is_zero():
        return None
    expr, modulus = lhs.args()
    if (
        not modulus.is_int_constant()
        or modulus.constant_value() != ARGS().field_type.value
    ):
        return None
    p = ARGS().field_type.value
    assert isprime(p), f"field modulus must be prime for rewrite_choice_simple, got {p}"
    factors = _flatten_times_factors(expr)
    if factors is not None:
        solved = _solved_roots(factors, p)
        if solved is not None:
            return roots_with_range(*solved)
        return Or(*[Equals(Mod(f, modulus), Int(0)) for f in factors])
    solved = _solved_quadratic(expr, p)
    if solved is not None:
        x, values = solved
        if not values:
            return FALSE()
        return roots_with_range(x, values)
    return None


def rewrite_z3simplify(node_type: int, args: list[FNode]) -> FNode:
    node = get_env().formula_manager.create_node(node_type, tuple(args))
    res = z3_simplify(node)
    return res if res != node else None


def rewrite_simplify(node_type: int, args: list[FNode]) -> FNode:
    node = get_env().formula_manager.create_node(node_type, tuple(args))
    res = simplify(node)
    if res != node:
        return res
    return None


class IntConstantReducer(substituter.Substituter):
    def __init__(self, modulus, env=None):
        """Create a PySMT substituter that may rewrite equalities via SymPy."""
        substituter.Substituter.__init__(self, env=env)
        self.modulus = modulus

    def walk_int_constant(self, formula, args, **kwargs):
        v = formula.constant_value()
        if v <= -self.modulus or v >= self.modulus:
            return Int(v % self.modulus)
        return formula
    
    def walk_mod(self, formula, args, **kwargs):
        if args[1].is_int_constant(self.modulus):
            return Mod(args[0], Int(self.modulus))
        return formula


def rewrite_mod(node_type: int, args: list[FNode]) -> FNode:
    assert node_type == operators.MOD
    expr, modulus = args
    if not modulus.is_int_constant():
        return None
    expr = IntConstantReducer(modulus.constant_value()).substitute(expr)

    if modulus.is_int_constant(ARGS().field_type.value) and expr.is_symbol():
        return expr
    return Mod(expr, modulus)
