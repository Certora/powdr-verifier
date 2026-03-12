from textwrap import dedent

from src.simplify import simplify_intervals
from src.smt.utils import *


def _has_mod(f: FNode) -> bool:
    if f.is_mod():
        return True
    return any(_has_mod(a) for a in f.args())


def _is_or_has_conjunct(f: FNode, expected: FNode) -> bool:
    return f == expected or (f.is_and() and expected in f.args())


def _has_any_conjunct(f: FNode, expected: list[FNode]) -> bool:
    if f in expected:
        return True
    if not f.is_and():
        return False
    return any(c in expected for c in f.args())


def _asserts_from_script(smt: str) -> list[FNode]:
    parser = SmtLibParser()
    smt_script = parser.get_script(StringIO(dedent(smt).strip() + "\n"))
    simplified = simplify_intervals(smt_script)
    return [cmd.args[0] for cmd in simplified if cmd.name == "assert"]


def test_interval_refinement_from_simple_inequalities():
    true_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (< x 16))
        (assert (<= x 15))
        (check-sat)
        """
    )
    x = Symbol("x", INT)
    assert _is_or_has_conjunct(true_asserts[2], LE(Int(0), x))
    assert _is_or_has_conjunct(true_asserts[2], LE(x, Int(15)))

    false_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (< x 16))
        (assert (< x 0))
        (check-sat)
        """
    )
    assert false_asserts[2].is_false()


def test_eval_bool_with_arithmetic_product_bounds():
    true_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= 0 x))
        (assert (<= x 3))
        (assert (<= 0 y))
        (assert (<= y 4))
        (assert (<= (* x y) 12))
        (check-sat)
        """
    )
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    assert _is_or_has_conjunct(true_asserts[4], LE(Int(0), x))
    assert _is_or_has_conjunct(true_asserts[4], LE(x, Int(3)))
    assert _is_or_has_conjunct(true_asserts[4], LE(Int(0), y))
    assert _is_or_has_conjunct(true_asserts[4], LE(y, Int(4)))

    false_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= 0 x))
        (assert (<= x 3))
        (assert (<= 0 y))
        (assert (<= y 4))
        (assert (< (* x y) 0))
        (check-sat)
        """
    )
    assert false_asserts[4].is_false()

    unknown_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= 0 x))
        (assert (<= x 3))
        (assert (<= 0 y))
        (assert (<= y 4))
        (assert (= (* x y) 7))
        (check-sat)
        """
    )
    assert _is_or_has_conjunct(unknown_asserts[4], Equals(x * y, Int(7)))


def test_eval_bool_with_addition_and_subtraction():
    true_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= 10 a))
        (assert (<= a 20))
        (assert (<= 3 b))
        (assert (<= b 5))
        (assert (<= 5 (- a b)))
        (check-sat)
        """
    )
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    assert _is_or_has_conjunct(true_asserts[4], LE(Int(10), a))
    assert _is_or_has_conjunct(true_asserts[4], LE(a, Int(20)))
    assert _is_or_has_conjunct(true_asserts[4], LE(Int(3), b))
    assert _is_or_has_conjunct(true_asserts[4], LE(b, Int(5)))

    false_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= 10 a))
        (assert (<= a 20))
        (assert (<= 3 b))
        (assert (<= b 5))
        (assert (< (- a b) 5))
        (check-sat)
        """
    )
    assert false_asserts[4].is_false()

    unknown_asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= 10 a))
        (assert (<= a 20))
        (assert (<= 3 b))
        (assert (<= b 5))
        (assert (= (+ a b) 18))
        (check-sat)
        """
    )
    assert _has_any_conjunct(
        unknown_asserts[4],
        [
            Equals(a + b, Int(18)),
            Equals(b + a, Int(18)),
        ],
    )


def test_simplify_intervals_removes_mod_when_no_overflow():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (<= x 100))
        (assert (mod x {p}))
        (check-sat)
        """
    )
    target = asserts[2]
    x = Symbol("x", INT)
    assert not _has_mod(target)
    assert target == x


def test_simplify_intervals_keeps_mod_when_negative_possible():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= 0 x))
        (assert (<= x 100))
        (assert (<= 0 y))
        (assert (<= y 100))
        (assert (mod (- x y) {p}))
        (check-sat)
        """
    )
    target = asserts[4]
    assert _has_mod(target)


def test_mod_zero_to_eq_zero_in_injective_window():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= -5 x))
        (assert (<= x 5))
        (assert (= (mod x {p}) 0))
        (check-sat)
        """
    )
    x = Symbol("x", INT)
    assert any(a == Equals(x, Int(0)) for a in asserts)
