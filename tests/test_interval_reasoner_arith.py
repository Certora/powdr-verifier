from src.simplify import simplify_intervals
from src.smt.utils import *


def _has_mod(f: FNode) -> bool:
    if f.is_mod():
        return True
    return any(_has_mod(a) for a in f.args())


def _asserts_from_script(smt: str) -> list[FNode]:
    parser = SmtLibParser()
    smt_script = parser.get_script(StringIO(smt))
    simplified = simplify_intervals(smt_script)
    return [cmd.args[0] for cmd in simplified if cmd.name == "assert"]


def test_interval_refinement_from_simple_inequalities():
    true_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (< x 16))\n"
        "(assert (<= x 15))\n"
        "(check-sat)\n"
    )
    assert true_asserts[2].is_true()

    false_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (< x 16))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n"
    )
    assert false_asserts[2].is_false()


def test_eval_bool_with_arithmetic_product_bounds():
    true_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 3))\n"
        "(assert (<= 0 y))\n"
        "(assert (<= y 4))\n"
        "(assert (<= (* x y) 12))\n"
        "(check-sat)\n"
    )
    assert true_asserts[4].is_true()

    false_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 3))\n"
        "(assert (<= 0 y))\n"
        "(assert (<= y 4))\n"
        "(assert (< (* x y) 0))\n"
        "(check-sat)\n"
    )
    assert false_asserts[4].is_false()

    unknown_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 3))\n"
        "(assert (<= 0 y))\n"
        "(assert (<= y 4))\n"
        "(assert (= (* x y) 7))\n"
        "(check-sat)\n"
    )
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    assert unknown_asserts[4] == Equals(x * y, Int(7))


def test_eval_bool_with_addition_and_subtraction():
    true_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 10 a))\n"
        "(assert (<= a 20))\n"
        "(assert (<= 3 b))\n"
        "(assert (<= b 5))\n"
        "(assert (<= 5 (- a b)))\n"
        "(check-sat)\n"
    )
    assert true_asserts[4].is_true()

    false_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 10 a))\n"
        "(assert (<= a 20))\n"
        "(assert (<= 3 b))\n"
        "(assert (<= b 5))\n"
        "(assert (< (- a b) 5))\n"
        "(check-sat)\n"
    )
    assert false_asserts[4].is_false()

    unknown_asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 10 a))\n"
        "(assert (<= a 20))\n"
        "(assert (<= 3 b))\n"
        "(assert (<= b 5))\n"
        "(assert (= (+ a b) 18))\n"
        "(check-sat)\n"
    )
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    assert unknown_asserts[4] == Equals(a + b, Int(18))


def test_simplify_intervals_removes_mod_when_no_overflow():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 100))\n"
        f"(assert (mod x {p}))\n"
        "(check-sat)\n"
    )
    target = asserts[2]
    x = Symbol("x", INT)
    assert not _has_mod(target)
    assert target == x


def test_simplify_intervals_keeps_mod_when_negative_possible():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 100))\n"
        "(assert (<= 0 y))\n"
        "(assert (<= y 100))\n"
        f"(assert (mod (- x y) {p}))\n"
        "(check-sat)\n"
    )
    target = asserts[4]
    assert _has_mod(target)


def test_mod_zero_to_eq_zero_in_injective_window():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= -5 x))\n"
        "(assert (<= x 5))\n"
        f"(assert (= (mod x {p}) 0))\n"
        "(check-sat)\n"
    )
    x = Symbol("x", INT)
    assert any(a == Equals(x, Int(0)) for a in asserts)
