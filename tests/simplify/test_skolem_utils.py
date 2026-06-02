from src.simplify.skolem_utils import split_equation
from src.smt.utils import *


def test_split_equation_equals():
    x, y = Symbol("sx", INT), Symbol("sy", INT)
    assert split_equation(Equals(x, y)) == (x, y)
    assert split_equation(Equals(Int(1), x)) == (x, Int(1))


def test_split_equation_iff_bool():
    a, b = Symbol("sa", BOOL), Symbol("sb", BOOL)
    assert split_equation(Iff(a, b)) == (a, b)
    assert split_equation(Iff(FALSE(), a)) == (a, FALSE())


def test_split_equation_iff_no_symbol_side():
    assert split_equation(Iff(TRUE(), TRUE())) is None


def test_split_equation_rejects_non_pin_shape():
    assert split_equation(Or(TRUE(), FALSE())) is None
