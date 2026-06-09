from pysmt import operators

from src.rewriter.rewrites import rewrite_choice_simple
from src.smt.utils import *
from src.utils.args import parse_args


def test_rewrite_choice_simple_equivalent_mod_zero():
    parse_args(["check", "x"])
    p = ARGS().field_type.value

    for a_val in range(min(p, 32)):
        for b_val in range(min(p, 32)):
            a = Int(a_val)
            b = Int(b_val)
            prod_zero = Equals(Mod(Times(a, b), Int(p)), Int(0))
            split_zero = rewrite_choice_simple(
                operators.EQUALS, [Mod(Times(a, b), Int(p)), Int(0)]
            )
            assert split_zero is not None
            if prod_zero.is_true() != split_zero.is_true():
                raise AssertionError((a_val, b_val, prod_zero, split_zero))


def test_rewrite_choice_simple_splits_non_atomic_products():
    # single-variable linear factors are solved to roots with the
    # implied range attached: (x = p-1 | x = p-2) & p-2 <= x <= p-1
    parse_args(["check", "x"])
    p = ARGS().field_type.value
    x = Symbol("x", INT)
    rew = rewrite_choice_simple(
        operators.EQUALS,
        [Mod(Times(Plus(x, Int(1)), Plus(x, Int(2))), Int(p)), Int(0)],
    )
    assert rew is not None and rew.is_and()
    disj = rew.arg(0)
    assert disj.is_or() and len(disj.args()) == 2
    roots = {d.arg(1).constant_value() for d in disj.args()}
    assert roots == {p - 1, p - 2}
    bounds = {a.serialize() for a in rew.args()[1:]}
    assert len(bounds) == 2


def test_rewrite_choice_simple_keeps_multivar_products_as_congruences():
    parse_args(["check", "x"])
    p = ARGS().field_type.value
    x, y = Symbol("mx", INT), Symbol("my", INT)
    rew = rewrite_choice_simple(
        operators.EQUALS,
        [Mod(Times(x, y), Int(p)), Int(0)],
    )
    assert rew is not None and rew.is_or() and len(rew.args()) == 2
