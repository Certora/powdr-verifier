import logging
from ..utils.args import ARGS
from ..utils.profiling import simple_profile
from ..smt.utils import *

@simple_profile
def rewrite_z3simplify(node_type: int, args: list[FNode]) -> FNode:
    node = get_env().formula_manager.create_node(node_type, tuple(args))
    return z3_simplify(node)

@simple_profile
def rewrite_simplify(node_type: int, args: list[FNode]) -> FNode:
    node = get_env().formula_manager.create_node(node_type, tuple(args))
    res = simplify(node)
    if res != node:
        return res
    return None

@simple_profile
def rewrite_mod(node_type: int, args: list[FNode]) -> FNode:
    assert node_type == operators.MOD
    expr, modulus = args
    if expr.is_int_constant():
        return Int(expr.constant_value() % modulus.constant_value())
    if not modulus.is_int_constant() or modulus.constant_value() != ARGS().field_type.value:
        return None
    if expr.is_symbol():
        return expr
    return None

@simple_profile
def rewrite_eqmod(node_type: int, args: list[FNode]) -> FNode:
    assert node_type == operators.EQUALS
    lhs, rhs = args
    if not lhs.is_mod() or not rhs.is_zero():
        return None
    expr, modulus = lhs.args()
    if not modulus.is_int_constant() or modulus.constant_value() != ARGS().field_type.value:
        return None
    if expr.is_plus() and len(expr.args()) == 2:
        a, b = expr.args()
        if a.is_int_constant() and b.is_symbol():
            return Equals(b, wrap_mod(Int(-a.constant_value())))
        if a.is_symbol() and b.is_int_constant():
            return Equals(a, wrap_mod(Int(-b.constant_value())))
    if expr.is_minus() and len(expr.args()) == 2:
        a, b = expr.args()
        if a.is_int_constant() and b.is_symbol():
            return Equals(b, wrap_mod(Int(a.constant_value())))
        if a.is_symbol() and b.is_int_constant():
            return Equals(a, wrap_mod(Int(b.constant_value())))
