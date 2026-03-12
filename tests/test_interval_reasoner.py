from textwrap import dedent

from src.simplify import simplify_intervals
from src.smt.utils import *


def _has_mod(f: FNode) -> bool:
    if f.is_mod():
        return True
    return any(_has_mod(a) for a in f.args())


def _asserts_from_script(smt: str) -> list[FNode]:
    parser = SmtLibParser()
    smt_script = parser.get_script(StringIO(dedent(smt).strip() + "\n"))
    simplified = simplify_intervals(smt_script)
    return [cmd.args[0] for cmd in simplified if cmd.name == "assert"]


def test_recognize_inequalities_and_or_equalities():
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (< x 10))
        (assert (or (= x 2) (= x 3) (= x 4)))
        (assert (= x 9))
        (check-sat)
        """
    )
    assert asserts[3].is_false()


def test_mod_no_overflow_only_for_canonical_range():
    p = int(ARGS().field_type.value)

    safe_asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= 0 a))
        (assert (<= a 100))
        (assert (<= 0 b))
        (assert (<= b 100))
        (assert (mod a {p}))
        (check-sat)
        """
    )
    assert not _has_mod(safe_asserts[4])

    unsafe_asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= 0 a))
        (assert (<= a 100))
        (assert (<= 0 b))
        (assert (<= b 100))
        (assert (mod (- a b) {p}))
        (check-sat)
        """
    )
    assert _has_mod(unsafe_asserts[4])


def test_used_constraints_are_retained_under_pruning():
    x = Symbol("x", INT)
    f = Equals(x, Int(0))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= x 0))
        (check-sat)
        """
    )
    assert asserts[0] == f


def test_bound_deriving_formula_is_not_eliminated():
    x = Symbol("x", INT)
    bound = LE(x, Int(10))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= x 10))
        (assert (= 1 1))
        (check-sat)
        """
    )
    assert asserts[0] == bound
    assert asserts[1].is_true()


def test_field_bounds_0_and_p_are_not_eliminated():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    lower = LE(Int(0), x)
    upper = LT(x, Int(p))
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (< x {p}))
        (check-sat)
        """
    )
    assert asserts[0] == lower
    assert asserts[1] == upper


def test_simplify_intervals_can_append_derived_ranges():
    x = Symbol("x", INT)
    expected_range = And(LE(Int(0), x), LE(x, Int(10)))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= 0 x))
        (assert (<= x 10))
        (assert (= 1 1))
        (check-sat)
        """
    )
    assert asserts[2].is_true()
    assert any(c == expected_range for c in asserts)


def test_fixed_point_opcode_flags_sum_forces_all_zero():
    sub = Symbol("sub", INT)
    xor = Symbol("xor", INT)
    orf = Symbol("orf", INT)
    andf = Symbol("andf", INT)
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun sub () Int)
        (declare-fun xor () Int)
        (declare-fun orf () Int)
        (declare-fun andf () Int)
        (assert (or (= sub 0) (= sub 1)))
        (assert (or (= xor 0) (= xor 1)))
        (assert (or (= orf 0) (= orf 1)))
        (assert (or (= andf 0) (= andf 1)))
        (assert (= (+ sub (* 2 xor) (* 3 orf) (* 4 andf)) 0))
        (check-sat)
        """
    )
    assert any(a == Equals(sub, Int(0)) for a in asserts)
    assert any(a == Equals(xor, Int(0)) for a in asserts)
    assert any(a == Equals(orf, Int(0)) for a in asserts)
    assert any(a == Equals(andf, Int(0)) for a in asserts)


def test_fixed_point_requires_mod_elimination_before_affine_sum():
    p = int(ARGS().field_type.value)
    sub = Symbol("sub2", INT)
    xor = Symbol("xor2", INT)
    orf = Symbol("orf2", INT)
    andf = Symbol("andf2", INT)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun sub2 () Int)
        (declare-fun xor2 () Int)
        (declare-fun orf2 () Int)
        (declare-fun andf2 () Int)
        (assert (or (= sub2 0) (= sub2 1)))
        (assert (or (= xor2 0) (= xor2 1)))
        (assert (or (= orf2 0) (= orf2 1)))
        (assert (or (= andf2 0) (= andf2 1)))
        (assert (= (mod (+ sub2 (* 2 xor2) (* 3 orf2) (* 4 andf2)) {p}) 0))
        (check-sat)
        """
    )
    assert any(a == Equals(sub, Int(0)) for a in asserts)
    assert any(a == Equals(xor, Int(0)) for a in asserts)
    assert any(a == Equals(orf, Int(0)) for a in asserts)
    assert any(a == Equals(andf, Int(0)) for a in asserts)


def test_mod_zero_rewrites_to_unique_nonzero_multiple():
    p = int(ARGS().field_type.value)
    x = Symbol("x_unique_mult", INT)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun x_unique_mult () Int)
        (assert (<= {p - 2} x_unique_mult))
        (assert (<= x_unique_mult {p + 3}))
        (assert (= (mod x_unique_mult {p}) 0))
        (check-sat)
        """
    )
    assert any(a == Equals(x, Int(p)) for a in asserts)


def test_constraints_5_and_6_style_mods_are_removed():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"""
        (set-logic ALL)
        (declare-fun f0 () Int)
        (declare-fun f1 () Int)
        (declare-fun f2 () Int)
        (declare-fun f3 () Int)
        (assert (or (= f0 0) (= f0 1) (= f0 2)))
        (assert (or (= f1 0) (= f1 1) (= f1 2)))
        (assert (or (= f2 0) (= f2 1) (= f2 2)))
        (assert (or (= f3 0) (= f3 1) (= f3 2)))
        (assert (or (= (+ f0 f1 f2 f3) 0)
                    (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0)
                    (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))
        (assert (or (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0)
                    (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))
        (check-sat)
        """
    )
    assert all(not _has_mod(f) for f in asserts)


def test_derived_multi_interval_constraint_is_disjunction():
    x = Symbol("x_disj_domain", INT)
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x_disj_domain () Int)
        (assert (or (= x_disj_domain 0) (= x_disj_domain 1)))
        (assert true)
        (check-sat)
        """
    )
    expected = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    assert any(c == expected for c in asserts)


def test_exists_quantifier_injects_bounds_with_conjunction():
    x = Symbol("x_exists_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (assert (exists ((x_exists_inject Int))
                       (or (= x_exists_inject 0) (= x_exists_inject 1))))
        (check-sat)
        """
    )
    out = asserts[0]
    assert out.is_exists()
    injected = out.arg(0)
    assert injected.is_and()
    assert body in injected.args()
    assert Or(Equals(x, Int(0)), Equals(x, Int(1))) in injected.args()


def test_forall_quantifier_injects_body_bounds_with_conjunction():
    x = Symbol("x_forall_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (assert (forall ((x_forall_inject Int))
                       (or (= x_forall_inject 0) (= x_forall_inject 1))))
        (check-sat)
        """
    )
    out = asserts[0]
    assert out.is_forall()
    injected = out.arg(0)
    assert not injected.is_implies()
    assert injected == body or (injected.is_and() and body in injected.args())


def test_forall_quantifier_ignores_shadowed_outer_bounds():
    x = Symbol("x_forall_outer_guard", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun x_forall_outer_guard () Int)
        (assert (<= 0 x_forall_outer_guard))
        (assert (forall ((x_forall_outer_guard Int))
                       (or (= x_forall_outer_guard 0) (= x_forall_outer_guard 1))))
        (check-sat)
        """
    )
    print(asserts)
    out = asserts[1]
    assert out.is_forall()
    injected = out.arg(0)
    assert not injected.is_implies()
    assert injected == body or (injected.is_and() and body in injected.args())
    assert False


def test_forall_quantifier_uses_implication_for_nonshadowed_outer_bounds():
    x = Symbol("x_forall_nonshadowed_bound", INT)
    y = Symbol("y_forall_nonshadowed_bound", INT)
    body = Or(Equals(x, Int(0)), Equals(y, Int(1)))
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun y_forall_nonshadowed_bound () Int)
        (assert (<= 0 y_forall_nonshadowed_bound))
        (assert (forall ((x_forall_nonshadowed_bound Int))
                       (or (= x_forall_nonshadowed_bound 0)
                           (= y_forall_nonshadowed_bound 1))))
        (check-sat)
        """
    )
    out = asserts[1]
    assert out.is_forall()
    injected = out.arg(0)
    assert injected.is_implies()
    assert injected.arg(0) == LE(Int(0), y)
    consequence = injected.arg(1)
    assert consequence == body or (consequence.is_and() and body in consequence.args())


def test_quantifier_injection_only_uses_variables_present_in_body():
    y = Symbol("y_quant_scope", INT)
    asserts = _asserts_from_script(
        """
        (set-logic ALL)
        (declare-fun y_quant_scope () Int)
        (assert (= y_quant_scope 7))
        (assert (forall ((x_quant_scope Int)) (= x_quant_scope x_quant_scope)))
        (check-sat)
        """
    )
    out = asserts[1]
    assert y not in out.get_free_variables()
