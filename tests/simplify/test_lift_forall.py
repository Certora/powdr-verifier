from src.simplify.lift_forall import simplify_lift_forall
from src.smt.utils import *


def _script_assert(f):
    s = script.SmtLibScript()
    s.commands = [script.SmtLibCommand("assert", [f])]
    return s


def test_lift_single_var_drops_forall_keeps_body():
    x = Symbol("lx", INT)
    inner = Or(Not(Equals(x, Int(7))), LT(x, Int(0)))
    f = ForAll([x], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[0].args[0]
    assert out == inner
    assert f.is_forall() and list(f.quantifier_vars()) == [x]
    assert not out.is_forall()


def test_lift_two_vars_in_sequence():
    x, y = Symbol("lx2", INT), Symbol("ly2", INT)
    inner = Or(Not(Equals(x, Int(1))), Not(Equals(y, Int(2))), LT(y, x))
    f = ForAll([x, y], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[0].args[0]
    assert out == inner
    assert f.is_forall() and set(f.quantifier_vars()) == {x, y}
    assert not out.is_forall()


def test_skips_when_expr_mentions_other_quantified_var():
    x, y = Symbol("lsx", INT), Symbol("lsy", INT)
    inner = Or(Not(Equals(x, y)), LT(x, Int(0)))
    f = ForAll([x, y], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[0].args[0]
    assert out == f
    assert out.is_forall() and list(out.quantifier_vars()) == list(f.quantifier_vars())
