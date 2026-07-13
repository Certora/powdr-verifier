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


def _conjuncts(f: FNode) -> list[FNode]:
    return list(f.args()) if f.is_and() else [f]


def test_affine_ineq_neg_multivar_no_false_pass():
    """Regression: the coeff<0 branch of _refine_affine_ineq must project a lower
    bound from rest.lo, not rest.hi. On a >=2-variable inequality the two differ,
    and using rest.hi over-tightens -- deriving y>=10 from (x<=y, x in [0,10])
    instead of the sound y>=0 -- which collapses a satisfiable formula to `false`
    (a false PASS). Single-variable cases have rest.lo == rest.hi and mask the bug.
    """
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= 0 x))
        (assert (<= x 10))
        (assert (<= x y))
        (assert (<= y 5))
        (check-sat)
        """
    )
    # x=0,y=0 satisfies every assertion; the pass must NOT manufacture `false`.
    assert not any(a.is_false() for a in asserts)

    # And it must derive the SOUND lower bound y>=0, never the over-tight y>=10.
    y = Symbol("y", INT)
    all_conjuncts = [c for a in asserts for c in _conjuncts(a)]
    assert LE(Int(0), y) in all_conjuncts
    assert LE(Int(10), y) not in all_conjuncts


def test_mod_zero_product_multisym_no_false_pass():
    """Regression: prime-field product reasoning for (u1*..*uk)==0 (mod p) yields a
    DISJUNCTION (some factor == 0). A per-variable domain can only represent that as a
    single-variable value set, so the narrowing is sound only when every factor is a
    unit-affine term in ONE common symbol. For a genuine multi-symbol product the pass
    must DECLINE, not narrow each symbol to its own root (which asserts the unsound
    conjunction and can collapse a satisfiable formula to `false` -- a false PASS).
    """
    p = int(ARGS().field_type.value)
    # x*y == 0 (mod p), x,y in [0,p), plus x=3: SAT (x=3, y=0). Must not manufacture false.
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (and (<= 0 x) (< x {p})))
        (assert (and (<= 0 y) (< y {p})))
        (assert (= (mod (* x y) {p}) 0))
        (assert (= x 3))
        (check-sat)
        """
    )
    assert not any(a.is_false() for a in asserts)


def test_mod_zero_product_single_symbol_still_narrows():
    """The intended single-variable case must keep working: x*(x-3)==0 (mod p) over
    x in [0,p) narrows x to {0,3}, so adding x=5 is then infeasible (-> false)."""
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (and (<= 0 x) (< x {p})))
        (assert (= (mod (* x (- x 3)) {p}) 0))
        (assert (= x 5))
        (check-sat)
        """
    )
    assert any(a.is_false() for a in asserts)


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
