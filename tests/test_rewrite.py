from src.rewriter import rewrite
from src.smt.utils import *
from src.utils.args import parse_args

def test_rewrite():
    parse_args()

    a = Symbol("a", INT)
    b = Symbol("b", INT)
    c = Symbol("c", INT)
    d = Symbol("d", INT)
    e = Symbol("e", INT)

    input = Equals(
        wrap_mod(
            (
                Int(512) + (((((Int(0) + (a * Int(0))) + (b * Int(1))) + (c * Int(2))) + (d * Int(3))) + (e * Int(4)))
            ) - Int(512)
        ),
        Int(0)
    )

    assert rewrite(input) == Equals(
        wrap_mod(Plus(b, Int(2) * c, Int(3) * d, Int(4) * e)),
        Int(0)
    )

def test_solve_eqs():
    parse_args([])

    a = Symbol("a", INT)
    b = Symbol("b", INT)

    eq = Equals(wrap_mod(a + (Int(-1) * b)), Int(0))

    assert rewrite(eq) == Equals(a, b)
