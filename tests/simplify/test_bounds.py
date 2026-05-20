from src.simplify.bounds import simplify_bounds
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


def test_bounds_leaves_quantifiers_unchanged():
    x = Symbol("x@0", INT)
    y = Symbol("y@0", INT)
    smt_script = _script(ForAll([x], Equals(x, y)))

    simplified = simplify_bounds(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert field_symbol(y) in asserts
    assert ForAll([x], Equals(x, y)) in asserts
    assert all(not a.is_forall() or not a.arg(0).is_implies() for a in asserts)
