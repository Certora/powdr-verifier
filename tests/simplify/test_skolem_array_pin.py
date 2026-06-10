from src.simplify.lift_forall import simplify_lift_forall
from src.simplify.skolem import SkolemMap
from src.simplify import skolem_derived
from src.smt.utils import *
from src.verify import SetInfos, SkolemPin, SkolemPinKind


def test_skolem_map_accepts_array_qvar_pin():
    at = ArrayType(INT, INT)
    q_mem = Symbol("q_sk_arr", at)
    free_mem = Symbol("free_sk_arr", at)
    m = SkolemMap([q_mem])
    assert m.pin(q_mem, free_mem, source="unit")
    assert m.emit_disjuncts() == [Not(Equals(q_mem, free_mem))]


def test_skolem_derived_array_pin_hoists_via_lift_forall():
    at = ArrayType(INT, INT)
    q_mem = Symbol("after_sk_arr", at)
    free_mem = Symbol("before_sk_arr", at)
    inner = Or(LT(Select(q_mem, Int(0)), Int(99)), TRUE())
    forall = ForAll([q_mem], inner)
    m = SkolemMap([q_mem])
    skolem_derived.contribute(
        m,
        SetInfos(equations=[SkolemPin(Equals(q_mem, free_mem), SkolemPinKind.DERIVED)]),
    )
    assert m.is_pinned(q_mem) and m.pins[q_mem] == free_mem
    disj = m.emit_disjuncts()
    new_body = Or(*inner.args(), *disj)
    wrapped = ForAll([q_mem], new_body)
    smt = script.SmtLibScript()
    smt.commands = [
        script.SmtLibCommand("declare-fun", [free_mem]),
        script.SmtLibCommand("assert", [wrapped]),
    ]
    simplify_lift_forall(smt)
    top_asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert Equals(q_mem, free_mem) in top_asserts
    assert not top_asserts[-1].is_forall()
