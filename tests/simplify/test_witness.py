from src.simplify.witness import simplify_witnesses
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_witness_maps_expanded_markers_to_collapsed_free_var():
    a0 = Symbol("after-a__0@0", INT)
    a1 = Symbol("after-a__1@1", INT)
    cmp = Symbol("after-cmp@2", INT)
    free = Symbol("after-w@3", INT)
    b0 = Symbol("before-a__0@0", INT)
    b1 = Symbol("before-a__1@1", INT)
    bcmp = Symbol("before-cmp@2", INT)
    d0 = Symbol("before-u@4", INT)
    d1 = Symbol("before-v@5", INT)
    field = Int(ARGS().field_type.value)

    collapsed = Equals(
        Mod(Plus(Times(free, Plus(a0, a1)), Times(Int(-1), cmp)), field),
        Int(0),
    )
    expanded = Equals(
        Mod(Plus(Times(b0, d0), Times(b1, d1), Times(Int(-1), bcmp)), field),
        Int(0),
    )
    body = Or(Not(expanded), Equals(bcmp, cmp))

    simplified = simplify_witnesses(_script(collapsed, ForAll([d0, d1], body)))
    out = simplified.commands[1].args[0]

    assert not out.is_forall()
    assert d0 not in out.get_free_variables()
    assert d1 not in out.get_free_variables()
    assert free in out.get_free_variables()
