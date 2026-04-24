from src.simplify.bounds import simplify_bounds
from src.simplify.lift_forall import simplify_lift_forall
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_bounds_adds_top_level_asserts_for_matching_free_vars():
    x = Symbol("x@0", INT)
    y = Symbol("y", INT)
    smt_script = _script(Equals(x, y))

    simplified = simplify_bounds(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert asserts == [field_symbol(x), Equals(x, y)]


def test_bounds_injects_forall_bounds_inside_quantifier():
    x = Symbol("x@0", INT)
    y = Symbol("y", INT)
    smt_script = _script(ForAll([x], Equals(x, y)))

    simplified = simplify_bounds(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert asserts == [ForAll([x], Implies(field_symbol(x), Equals(x, y)).simplify())]


def test_bounds_injects_exists_bounds_inside_quantifier():
    x = Symbol("x@0", INT)
    y = Symbol("y", INT)
    smt_script = _script(Exists([x], Equals(x, y)))

    simplified = simplify_bounds(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert asserts == [Exists([x], And(field_symbol(x), Equals(x, y)).simplify())]


def test_bounds_after_lift_adds_bounds_for_lifted_vars():
    x = Symbol("x@0", INT)
    y = Symbol("y", INT)
    smt_script = _script(ForAll([x], Or(Not(Equals(x, Int(7))), LT(y, Int(0)))))

    lifted = simplify_lift_forall(smt_script)
    bounded = simplify_bounds(lifted)
    asserts = [cmd.args[0] for cmd in bounded if cmd.name == "assert"]

    assert field_symbol(x) in asserts
    assert Equals(x, Int(7)) in asserts
    assert LT(y, Int(0)) in asserts
