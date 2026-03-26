from src.simplify import simplify_intervals
from src.simplify.intervals import simplify_intervals2
from src.simplify.intervals import Interval, IntervalReasoner
from src.smt.utils import *
from textwrap import dedent


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


def test_simplify_intervals_or_negations():
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (assert
                    (forall ((a Int) (x Int) (y Int) (z Int))
                        (or
                            (not (<= 0 a))
                            (not (<= 0 x))
                            (not (<= 0 y))
                            (not (<= 0 z))
                            (<= 2013265921 a)
                            (<= 2013265921 x)
                            (<= 2013265921 y)
                            (<= 2013265921 z)
                            (or
                                (not (or (= x 1) (= x 0)))
                                (not (or (= y 1) (= y 0)))
                                (not (or (= z 1) (= z 0)))
                                (not
                                    (=
                                        (mod
                                            (+
                                                x
                                                (* 2 y)
                                                (* 3 z)
                                            )
                                            2013265921
                                        )
                                        0
                                    )
                                )
                            )
                            (not 
                                (=
                                    (mod
                                        (+ a x y z (- 1))
                                        2013265921
                                    )
                                    0
                                )
                            )
                        )
                    )
                )
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert len(asserts) == 1

    x = Symbol("x", INT)
    y = Symbol("y", INT)
    z = Symbol("z", INT)
    out = asserts[0]
    assert out.is_forall()
    body = out.arg(0)
    assert body.is_or()

    def _disjunct_is_not_triple_zero(d: FNode) -> bool:
        if not d.is_not():
            return False
        a = d.arg(0)
        if not a.is_and() or len(list(a.args())) != 3:
            return False
        syms = set()
        for eq in a.args():
            if not eq.is_equals():
                return False
            u, v = eq.args()
            if v != Int(0) or not u.is_symbol():
                return False
            syms.add(u)
        return syms == {x, y, z}

    assert any(_disjunct_is_not_triple_zero(d) for d in body.args())

def test_simplify_intervals_marks_obvious_inconsistency():
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= x 1))
                (assert (<= 3 x))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert asserts
    assert all(a.is_false() for a in asserts)


def test_simplify_intervals2_marks_obvious_inconsistency():
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= x 1))
                (assert (<= 3 x))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_intervals2(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert asserts
    assert all(a.is_false() for a in asserts)


def test_simplify_intervals_retains_only_strengthening_bounds():
    x = Symbol("x", INT)
    parser = SmtLibParser()
    script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= 0 x))
                (assert (<= x 10))
                (assert (= (mod x 17) (mod x 17)))
                (check-sat)
                """
            ).strip()
            + "\n"
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
            dedent(
                f"""
                (set-logic ALL)
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun c () Int)
                (assert (= (mod (- 1 (+ a (* 256 b) (* 65536 c))) {p}) 0))
                (assert (<= 0 a))
                (assert (<= 0 b))
                (assert (<= 0 c))
                (assert (< a 256))
                (assert (< b 256))
                (assert (< c {p}))
                (assert (= (mod (* c (- 255 c)) {p}) 0))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_intervals(script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    a_sym = Symbol("a", INT)
    b_sym = Symbol("b", INT)

    assert any(a0 == Equals(a_sym, Int(1)) or (a0.is_and() and Equals(a_sym, Int(1)) in a0.args()) for a0 in asserts)
    assert any(a0 == Equals(b_sym, Int(0)) or (a0.is_and() and Equals(b_sym, Int(0)) in a0.args()) for a0 in asserts)
