import sympy

from ..smt.utils import *

def to_sympy(expr: FNode) -> sympy.Expr:
    if expr.is_true():
        return sympy.true
    if expr.is_false():
        return sympy.false
    if expr.is_symbol():
        return sympy.Symbol(expr.symbol_name())
    elif expr.is_and():
        return sympy.And(*[to_sympy(arg) for arg in expr.args()])
    elif expr.is_or():
        return sympy.Or(*[to_sympy(arg) for arg in expr.args()])
    elif expr.is_not():
        return sympy.Not(to_sympy(expr.args()[0]))
    elif expr.is_implies():
        return sympy.Implies(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_iff():
        return sympy.Equivalent(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_equals():
        return sympy.Eq(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_lt():
        return sympy.Lt(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_le():
        return sympy.Le(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_mod():
        return sympy.Mod(to_sympy(expr.args()[0]), to_sympy(expr.args()[1]))
    elif expr.is_int_constant():
        return sympy.Integer(expr.constant_value())
    elif expr.is_plus():
        return sympy.Add(*[to_sympy(arg) for arg in expr.args()])
    elif expr.is_minus():
        first, *tail = expr.args()
        return sympy.Add(to_sympy(first), *[-to_sympy(arg) for arg in tail])
    elif expr.is_times():
        return sympy.Mul(*[to_sympy(arg) for arg in expr.args()])
    elif expr.is_function_application():
        return sympy.Function(expr.function_name().symbol_name())(*[to_sympy(arg) for arg in expr.args()])
    else:
        assert False, f"Unknown expression type: {expr}"

def to_smt(expr: sympy.Expr) -> FNode:
    if expr == sympy.true:
        return TRUE()
    elif expr == sympy.false:
        return FALSE()
    elif isinstance(expr, sympy.Symbol):
        return get_env().formula_manager.symbols[expr.name]
    elif isinstance(expr, sympy.Integer):
        return Int(int(expr))
    elif isinstance(expr, sympy.And):
        return And(*[to_smt(arg) for arg in expr.args])
    elif isinstance(expr, sympy.Or):
        return Or(*[to_smt(arg) for arg in expr.args])
    elif isinstance(expr, sympy.Equality):
        return Equals(to_smt(expr.lhs), to_smt(expr.rhs))
    elif isinstance(expr, sympy.Lt):
        return LT(to_smt(expr.lhs), to_smt(expr.rhs))
    elif isinstance(expr, sympy.Le):
        return LE(to_smt(expr.lhs), to_smt(expr.rhs))
    elif isinstance(expr, sympy.Integer):
        return Int(int(expr))
    elif isinstance(expr, sympy.Add):
        return Plus(*[to_smt(arg) for arg in expr.args])
    elif isinstance(expr, sympy.Mul):
        return Times(*[to_smt(arg) for arg in expr.args])
    elif isinstance(expr, sympy.Mod):
        return Mod(to_smt(expr.args[0]), to_smt(expr.args[1]))
    elif isinstance(expr, sympy.Pow):
        return Times([to_smt(expr.base)] * int(expr.exp))
    elif isinstance(expr, sympy.Function):
        fs = Symbol(expr.name, FunctionType(INT, [INT] * len(expr.args)))
        return Function(fs, [to_smt(arg) for arg in expr.args])
    else:
        assert False, f"Unknown expression type: {expr}"
