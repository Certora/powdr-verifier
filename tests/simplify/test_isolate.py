from src.simplify.isolate import simplify_isolate
from src.simplify.lift_forall import simplify_lift_forall
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_isolate_adds_liftable_model_for_local_quantified_var():
    x = Symbol("isolated_x", INT)
    y = Symbol("external_y", INT)
    body = Or(LE(x, Int(0)), LE(Int(10), x), LT(y, Int(0)))
    smt_script = _script(ForAll([x], body))

    isolated = simplify_isolate(smt_script)
    lifted = simplify_lift_forall(isolated)
    out = lifted.commands[-1].args[0]

    assert not out.is_forall()
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == x
    ]
    assert pins
