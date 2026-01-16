from typing import Optional, TextIO

from z3 import *
from z3.z3util import *
from z3.z3printer import *

from ..utils import ARGS

FNode = AstRef
Logic = str

UFNIA = "UFNIA"
QF_UFNIA = "QF_UFNIA"

set_param("smtlib2_compliant", True)
set_param("pp.fixed_indent", True)
set_param("pp.flat_assoc", False)
set_param("pp.min_alias_size", 1000)

set_option(smtlib2_compliant=True)
set_option(fixed_indent=True)
set_option(flat_assoc=False)
set_option(min_alias_size=1000)

def Int(value: int) -> FNode:
    return IntVal(value)

def wrap_mod(input: FNode, modulus: Optional[FNode] = None) -> FNode:
    if modulus is None:
        modulus = IntVal(ARGS().field_type.value)
    return input % modulus

def call_fun(fun: FNode, args: list[FNode]) -> FNode:
    return fun(*args)

def And(*args: FNode) -> FNode:
    if args:
        return z3.And(*args)
    return BoolVal(True)

def Plus(left: FNode, right: FNode) -> FNode:
    return left + right
def Minus(left: FNode, right: FNode) -> FNode:
    return left - right
def Times(left: FNode, right: FNode) -> FNode:
    return left * right
def Equals(left: FNode, right: FNode) -> FNode:
    return left == right
def LE(left: FNode, right: FNode) -> FNode:
    return left <= right
def LT(left: FNode, right: FNode) -> FNode:
    return left < right
def GE(left: FNode, right: FNode) -> FNode:
    return left >= right
def GT(left: FNode, right: FNode) -> FNode:
    return left > right

def TRUE() -> FNode:
    return BoolVal(True)

def is_int_constant(f: FNode) -> bool:
    return is_int_value(f)

def size(f: FNode) -> int:
    return 1 + sum(size(child) for child in f.children())

def is_valid(s: Solver, f: FNode) -> bool:
    s.push()
    s.add(Not(f))
    print(s.to_smt2())
    result = s.check()
    s.pop()
    return result == unsat

def is_sat(s: Solver, f: FNode) -> bool:
    s.push()
    s.add(f)
    result = s.check()
    s.pop()
    return result == sat

def print_formula_to_file(s, LOGIC, dump):
    print(f"dumping to {dump.name}")
    dump.write(s.to_smt2())
