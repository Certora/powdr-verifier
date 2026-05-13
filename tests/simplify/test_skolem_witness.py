from src.simplify.skolem import SkolemMap
from src.simplify.skolem_witness import collect_candidates, contribute
from src.smt.utils import *
from src.utils.args import parse_args


def test_partial_collapsed_diff_inv_still_collects_witness_candidate():
    parse_args(["simplify", "/tmp/x", "nnf", "/tmp/y"])
    p = ARGS().field_type.value
    c = 2013265888
    a0a = Symbol("after-a__0_1@46", INT)
    a1a = Symbol("after-a__1_1@47", INT)
    a2a = Symbol("after-a__2_1@48", INT)
    a3a = Symbol("after-a__3_1@49", INT)
    m0a = Symbol("after-diff_inv_marker__0_1@58", INT)
    fv = Symbol("after-free_var_64@64", INT)
    cmp_a = Symbol("after-cmp_result_1@54", INT)

    collapsed = Equals(
        Mod(
            Plus(
                Times(Plus(a0a, Int(c)), m0a),
                Times(fv, Plus(Plus(a1a, a2a), a3a)),
                Times(Int(p - 1), cmp_a),
            ),
            Int(p),
        ),
        Int(0),
    )

    a0b = Symbol("before-a__0_1@46", INT)
    a1b = Symbol("before-a__1_1@47", INT)
    a2b = Symbol("before-a__2_1@48", INT)
    a3b = Symbol("before-a__3_1@49", INT)
    m0b = Symbol("before-diff_inv_marker__0_1@58", INT)
    m1b = Symbol("before-diff_inv_marker__1_1@59", INT)
    m2b = Symbol("before-diff_inv_marker__2_1@60", INT)
    m3b = Symbol("before-diff_inv_marker__3_1@61", INT)
    cmp_b = Symbol("before-cmp_result_1@54", INT)

    expanded = Equals(
        Mod(
            Plus(
                Times(Plus(a0b, Int(c)), m0b),
                Times(a1b, m1b),
                Times(a2b, m2b),
                Times(a3b, m3b),
                Times(Int(p - 1), cmp_b),
            ),
            Int(p),
        ),
        Int(0),
    )

    body = Or(Not(Equals(cmp_b, cmp_a)), expanded)
    forall = ForAll([m0b, m1b, m2b, m3b], body)

    smt = script.SmtLibScript()
    smt.commands = [
        script.SmtLibCommand("assert", [collapsed]),
        script.SmtLibCommand("assert", [forall]),
    ]

    cand = collect_candidates(smt)
    assert len(cand) == 1
    factors, cmp_key, free = cand[0]
    assert factors == frozenset(
        {"a__1_1@47", "a__2_1@48", "a__3_1@49"}
    )
    assert cmp_key == "cmp_result_1@54"
    assert free == fv

    m = SkolemMap([m0b, m1b, m2b, m3b])
    contribute(m, forall.arg(0), cand)
    assert m.is_pinned(m1b) and m.pins[m1b] == fv
    assert m.is_pinned(m2b) and m.pins[m2b] == fv
    assert m.is_pinned(m3b) and m.pins[m3b] == fv
    assert not m.is_pinned(m0b)


def test_witness_prefers_diff_inv_marker_when_limb_also_quantified():
    parse_args(["simplify", "/tmp/x", "nnf", "/tmp/y"])
    p = ARGS().field_type.value
    c = 2013265888
    a0a = Symbol("after-a__0_1@46", INT)
    a1a = Symbol("after-a__1_1@47", INT)
    a2a = Symbol("after-a__2_1@48", INT)
    a3a = Symbol("after-a__3_1@49", INT)
    m0a = Symbol("after-diff_inv_marker__0_1@58", INT)
    fv = Symbol("after-free_var_64@64", INT)
    cmp_a = Symbol("after-cmp_result_1@54", INT)

    collapsed = Equals(
        Mod(
            Plus(
                Times(Plus(a0a, Int(c)), m0a),
                Times(fv, Plus(Plus(a1a, a2a), a3a)),
                Times(Int(p - 1), cmp_a),
            ),
            Int(p),
        ),
        Int(0),
    )

    a0b = Symbol("before-a__0_1@46", INT)
    a1b = Symbol("before-a__1_1@47", INT)
    a2b = Symbol("before-a__2_1@48", INT)
    a3b = Symbol("before-a__3_1@49", INT)
    m0b = Symbol("before-diff_inv_marker__0_1@58", INT)
    m1b = Symbol("before-diff_inv_marker__1_1@59", INT)
    m2b = Symbol("before-diff_inv_marker__2_1@60", INT)
    m3b = Symbol("before-diff_inv_marker__3_1@61", INT)
    cmp_b = Symbol("before-cmp_result_1@54", INT)

    expanded = Equals(
        Mod(
            Plus(
                Times(Plus(a0b, Int(c)), m0b),
                Times(a1b, m1b),
                Times(a2b, m2b),
                Times(a3b, m3b),
                Times(Int(p - 1), cmp_b),
            ),
            Int(p),
        ),
        Int(0),
    )

    body = Or(Not(Equals(cmp_b, cmp_a)), expanded)
    forall = ForAll([m0b, m1b, m2b, m3b, a1b, a2b, a3b], body)

    smt = script.SmtLibScript()
    smt.commands = [
        script.SmtLibCommand("assert", [collapsed]),
        script.SmtLibCommand("assert", [forall]),
    ]

    cand = collect_candidates(smt)
    assert len(cand) == 1
    m = SkolemMap([m0b, m1b, m2b, m3b, a1b, a2b, a3b])
    contribute(m, forall.arg(0), cand)
    assert m.is_pinned(m1b) and m.pins[m1b] == fv
    assert not m.is_pinned(a1b)
