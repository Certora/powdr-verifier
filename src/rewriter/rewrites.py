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
    if factors is None:
        return None
    solved = _solved_roots(factors, p)
    if solved is not None:
        return roots_with_range(*solved)
    return Or(*[Equals(Mod(f, modulus), Int(0)) for f in factors])


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
