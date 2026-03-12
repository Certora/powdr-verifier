from src.simplify import simplify_intervals
from src.simplify.intervals import Interval, IntervalReasoner
from src.smt.utils import *


def test_fixed_point_backprop_on_affine_equality():
    x = Symbol("x_fp", INT)
    y = Symbol("y_fp", INT)
    engine = IntervalReasoner()
    assumptions = [
        Equals(x + y, Int(10)),
        LE(x, Int(3)),
        LE(Int(8), y),
        LE(y, Int(8)),
    ]

    engine.assume_all(assumptions)

    assert engine.get_interval(y) == Interval.const(8)
    assert engine.get_interval(x) == Interval.const(2)


def test_backprop_on_inequality_tightens_other_side():
    x = Symbol("x_ineq", INT)
    y = Symbol("y_ineq", INT)
    engine = IntervalReasoner()
    assumptions = [
        LE(Int(4), x),
        LE(x + y, Int(5)),
    ]

    engine.assume_all(assumptions)
    assert engine.get_interval(y).hi == 1


def test_default_domain_is_unbounded_integer():
    x = Symbol("x_unbounded", INT)
    engine = IntervalReasoner()
    assert engine.get_interval(x) == Interval.top()


def test_prime_field_range_eliminates_redundant_mod():
    p = int(ARGS().field_type.value)
    x = Symbol("x_mod", INT)
    engine = IntervalReasoner()
    # Mod is redundant once canonical range constraints are learned.
    engine.assume_all([LE(Int(0), x), LT(x, Int(p))])
    out = engine.simplify(Mod(x, Int(p)), prune=True)
    assert out == x


def test_simplify_intervals_marks_obvious_inconsistency():
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            "(set-logic ALL)\n"
            "(declare-fun x () Int)\n"
            "(assert (<= x 1))\n"
            "(assert (<= 3 x))\n"
            "(check-sat)\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert asserts
    assert all(a.is_false() for a in asserts)


def test_simplify_intervals_retains_only_strengthening_bounds():
    x = Symbol("x", INT)
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            "(set-logic ALL)\n"
            "(declare-fun x () Int)\n"
            "(assert (<= 0 x))\n"
            "(assert (<= x 10))\n"
            "(assert (= (mod x 17) (mod x 17)))\n"
            "(check-sat)\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    # Both bounds strengthen the initial unbounded domain and must be retained.
    assert any(a == LE(x, Int(10)) for a in asserts)
    assert any(a == LE(Int(0), x) for a in asserts)


def test_test_smt2_style_constraints_force_a_and_b():
    p = int(ARGS().field_type.value)
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    c = Symbol("c", INT)
    engine = IntervalReasoner(p=p)
    assumptions = [
        Equals(Mod(Int(1) - (a + Int(256) * b + Int(65536) * c), Int(p)), Int(0)),
        LE(Int(0), a),
        LE(Int(0), b),
        LE(Int(0), c),
        LT(a, Int(256)),
        LT(b, Int(256)),
        LT(c, Int(p)),
        Equals(Mod(c * (Int(255) - c), Int(p)), Int(0)),
    ]

    engine.assume_all(assumptions, max_iters=64)

    assert engine.get_interval(a) == Interval.const(1)
    assert engine.get_interval(b) == Interval.const(0)
    # In canonical field range this additionally pins c to 0.
    assert engine.get_interval(c) == Interval.const(0)


def test_simplify_intervals_emits_derived_equalities():
    p = int(ARGS().field_type.value)
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            "(set-logic ALL)\n"
            "(declare-fun a () Int)\n"
            "(declare-fun b () Int)\n"
            "(declare-fun c () Int)\n"
            f"(assert (= (mod (- 1 (+ a (* 256 b) (* 65536 c))) {p}) 0))\n"
            "(assert (<= 0 a))\n"
            "(assert (<= 0 b))\n"
            "(assert (<= 0 c))\n"
            "(assert (< a 256))\n"
            "(assert (< b 256))\n"
            f"(assert (< c {p}))\n"
            f"(assert (= (mod (* c (- 255 c)) {p}) 0))\n"
            "(check-sat)\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    a_sym = Symbol("a", INT)
    b_sym = Symbol("b", INT)

    assert any(a0 == Equals(a_sym, Int(1)) for a0 in asserts)
    assert any(a0 == Equals(b_sym, Int(0)) for a0 in asserts)
