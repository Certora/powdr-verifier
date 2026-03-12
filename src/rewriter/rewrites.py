import logging
from ..utils.args import ARGS
from ..utils.profiling import simple_profile
from ..smt.utils import *


def is_mul_by_minus_one(node: FNode) -> Optional[FNode]:
    if node.is_times() and len(node.args()) == 2:
        a, b = node.args()
        if a.is_int_constant(-1) or a.is_int_constant(ARGS().field_type.value - 1):
            return b
        if b.is_int_constant(-1) or b.is_int_constant(ARGS().field_type.value - 1):
            return a
    return None


@simple_profile
def rewrite_z3simplify(node_type: int, args: list[FNode]) -> FNode:
    node = get_env().formula_manager.create_node(node_type, tuple(args))
    res = z3_simplify(node)
    return res if res != node else None


@simple_profile
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


@simple_profile
def rewrite_mod(node_type: int, args: list[FNode]) -> FNode:
    assert node_type == operators.MOD
    expr, modulus = args
    if not modulus.is_int_constant():
        return None
    expr = IntConstantReducer(modulus.constant_value()).substitute(expr)

    if modulus.is_int_constant(ARGS().field_type.value) and expr.is_symbol():
        return expr
    return Mod(expr, modulus)


@simple_profile
def rewrite_eqmod(node_type: int, args: list[FNode]) -> FNode:
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
    if expr.is_plus() and len(expr.args()) == 2:
        a, b = expr.args()
        # c + s = 0 -> s = -c mod p
        if a.is_int_constant() and b.is_symbol():
            return Equals(b, wrap_mod(Int(-a.constant_value())))
        # s + c = 0 -> s = -c mod p
        if a.is_symbol() and b.is_int_constant():
            return Equals(a, wrap_mod(Int(-b.constant_value())))
        # -x + c = 0 -> c = x mod p
        # -x + s = 0 -> s = x mod p
        minusa = is_mul_by_minus_one(a)
        if minusa is not None and (b.is_symbol() or b.is_int_constant()):
            return Equals(b, wrap_mod(minusa))
        # c + -x = 0 -> c = x mod p
        # s + -x = 0 -> s = x mod p
        minusb = is_mul_by_minus_one(b)
        if minusb is not None and (a.is_symbol() or a.is_int_constant()):
            return Equals(a, wrap_mod(minusb))
    if expr.is_minus() and len(expr.args()) == 2:
        a, b = expr.args()
        # c - s = 0 -> s = c mod p
        if a.is_int_constant() and b.is_symbol():
            return Equals(b, wrap_mod(Int(a.constant_value())))
        # s - c = 0 -> s = c mod p
        if a.is_symbol() and b.is_int_constant():
            return Equals(a, wrap_mod(Int(b.constant_value())))
    return None
