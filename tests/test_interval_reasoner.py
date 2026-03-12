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


def test_recognize_inequalities_and_or_equalities():
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (< x 10))\n"
        "(assert (or (= x 2) (= x 3) (= x 4)))\n"
        "(assert (= x 9))\n"
        "(check-sat)\n"
    )

    # The disjunctive bounds force x into {2,3,4}, so x=9 is contradictory.
    assert asserts[3].is_false()


def test_mod_no_overflow_only_for_canonical_range():
    p = int(ARGS().field_type.value)

    safe_asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 0 a))\n"
        "(assert (<= a 100))\n"
        "(assert (<= 0 b))\n"
        "(assert (<= b 100))\n"
        f"(assert (mod a {p}))\n"
        "(check-sat)\n"
    )
    target_safe = safe_asserts[4]
    assert not _has_mod(target_safe)

    unsafe_asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 0 a))\n"
        "(assert (<= a 100))\n"
        "(assert (<= 0 b))\n"
        "(assert (<= b 100))\n"
        f"(assert (mod (- a b) {p}))\n"
        "(check-sat)\n"
    )
    target_unsafe = unsafe_asserts[4]
    assert _has_mod(target_unsafe)


def test_used_constraints_are_retained_under_pruning():
    x = Symbol("x", INT)
    f = Equals(x, Int(0))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 0))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == f


def test_bound_deriving_formula_is_not_eliminated():
    x = Symbol("x", INT)
    bound = LE(x, Int(10))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= x 10))\n"
        "(assert (= 1 1))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == bound
    assert asserts[1].is_true()


def test_field_bounds_0_and_p_are_not_eliminated():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    lower = LE(Int(0), x)
    upper = LT(x, Int(p))
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        f"(assert (< x {p}))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == lower
    assert asserts[1] == upper


def test_simplify_intervals_can_append_derived_ranges():
    x = Symbol("x", INT)
    expected_range = And(LE(Int(0), x), LE(x, Int(10)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 10))\n"
        "(assert (= 1 1))\n"
        "(check-sat)\n"
    )
    assert asserts[2].is_true()
    assert any(c == expected_range for c in asserts)


def test_fixed_point_opcode_flags_sum_forces_all_zero():
    sub = Symbol("sub", INT)
    xor = Symbol("xor", INT)
    orf = Symbol("orf", INT)
    andf = Symbol("andf", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun sub () Int)\n"
        "(declare-fun xor () Int)\n"
        "(declare-fun orf () Int)\n"
        "(declare-fun andf () Int)\n"
        "(assert (or (= sub 0) (= sub 1)))\n"
        "(assert (or (= xor 0) (= xor 1)))\n"
        "(assert (or (= orf 0) (= orf 1)))\n"
        "(assert (or (= andf 0) (= andf 1)))\n"
        "(assert (= (+ sub (* 2 xor) (* 3 orf) (* 4 andf)) 0))\n"
        "(check-sat)\n"
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
        f"(set-logic ALL)\n"
        "(declare-fun sub2 () Int)\n"
        "(declare-fun xor2 () Int)\n"
        "(declare-fun orf2 () Int)\n"
        "(declare-fun andf2 () Int)\n"
        "(assert (or (= sub2 0) (= sub2 1)))\n"
        "(assert (or (= xor2 0) (= xor2 1)))\n"
        "(assert (or (= orf2 0) (= orf2 1)))\n"
        "(assert (or (= andf2 0) (= andf2 1)))\n"
        f"(assert (= (mod (+ sub2 (* 2 xor2) (* 3 orf2) (* 4 andf2)) {p}) 0))\n"
        "(check-sat)\n"
    )
    assert any(a == Equals(sub, Int(0)) for a in asserts)
    assert any(a == Equals(xor, Int(0)) for a in asserts)
    assert any(a == Equals(orf, Int(0)) for a in asserts)
    assert any(a == Equals(andf, Int(0)) for a in asserts)


def test_mod_zero_rewrites_to_unique_nonzero_multiple():
    p = int(ARGS().field_type.value)
    x = Symbol("x_unique_mult", INT)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x_unique_mult () Int)\n"
        f"(assert (<= {p - 2} x_unique_mult))\n"
        f"(assert (<= x_unique_mult {p + 3}))\n"
        f"(assert (= (mod x_unique_mult {p}) 0))\n"
        "(check-sat)\n"
    )
    assert any(a == Equals(x, Int(p)) for a in asserts)


def test_constraints_5_and_6_style_mods_are_removed():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun f0 () Int)\n"
        "(declare-fun f1 () Int)\n"
        "(declare-fun f2 () Int)\n"
        "(declare-fun f3 () Int)\n"
        "(assert (or (= f0 0) (= f0 1) (= f0 2)))\n"
        "(assert (or (= f1 0) (= f1 1) (= f1 2)))\n"
        "(assert (or (= f2 0) (= f2 1) (= f2 2)))\n"
        "(assert (or (= f3 0) (= f3 1) (= f3 2)))\n"
        f"(assert (or (= (+ f0 f1 f2 f3) 0) (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0) (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))\n"
        f"(assert (or (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0) (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))\n"
        "(check-sat)\n"
    )
    assert all(not _has_mod(f) for f in asserts)


def test_derived_multi_interval_constraint_is_disjunction():
    x = Symbol("x_disj_domain", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x_disj_domain () Int)\n"
        "(assert (or (= x_disj_domain 0) (= x_disj_domain 1)))\n"
        "(assert true)\n"
        "(check-sat)\n"
    )
    expected = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    assert any(c == expected for c in asserts)


def test_exists_quantifier_injects_bounds_with_conjunction():
    x = Symbol("x_exists_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(assert (exists ((x_exists_inject Int)) (or (= x_exists_inject 0) (= x_exists_inject 1))))\n"
        "(check-sat)\n"
    )
    out = asserts[0]
    assert out.is_exists()
    injected = out.arg(0)
    assert injected.is_and()
    assert body in injected.args()
    assert Or(Equals(x, Int(0)), Equals(x, Int(1))) in injected.args()


def test_forall_quantifier_injects_bounds_with_implication_guard():
    x = Symbol("x_forall_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(assert (forall ((x_forall_inject Int)) (or (= x_forall_inject 0) (= x_forall_inject 1))))\n"
        "(check-sat)\n"
    )
    out = asserts[0]
    assert out.is_forall()
    injected = out.arg(0)
    assert injected.is_implies()
    assert injected.arg(0) == Or(Equals(x, Int(0)), Equals(x, Int(1)))
    assert injected.arg(1) == body


def test_quantifier_injection_only_uses_variables_present_in_body():
    y = Symbol("y_quant_scope", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun y_quant_scope () Int)\n"
        "(assert (= y_quant_scope 7))\n"
        "(assert (forall ((x_quant_scope Int)) (= x_quant_scope x_quant_scope)))\n"
        "(check-sat)\n"
    )
    out = asserts[1]
    # y is not present in quantifier body, so no bound for y may be injected there.
    assert y not in out.get_free_variables()
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


def test_recognize_inequalities_and_or_equalities():
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (< x 10))\n"
        "(assert (or (= x 2) (= x 3) (= x 4)))\n"
        "(assert (= x 9))\n"
        "(check-sat)\n"
    )

    # The disjunctive bounds force x into {2,3,4}, so x=9 is contradictory.
    assert asserts[3].is_false()


def test_mod_no_overflow_only_for_canonical_range():
    p = int(ARGS().field_type.value)

    safe_asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 0 a))\n"
        "(assert (<= a 100))\n"
        "(assert (<= 0 b))\n"
        "(assert (<= b 100))\n"
        f"(assert (mod a {p}))\n"
        "(check-sat)\n"
    )
    target_safe = safe_asserts[4]
    assert not _has_mod(target_safe)

    unsafe_asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (<= 0 a))\n"
        "(assert (<= a 100))\n"
        "(assert (<= 0 b))\n"
        "(assert (<= b 100))\n"
        f"(assert (mod (- a b) {p}))\n"
        "(check-sat)\n"
    )
    target_unsafe = unsafe_asserts[4]
    assert _has_mod(target_unsafe)


def test_used_constraints_are_retained_under_pruning():
    x = Symbol("x", INT)
    f = Equals(x, Int(0))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 0))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == f


def test_bound_deriving_formula_is_not_eliminated():
    x = Symbol("x", INT)
    bound = LE(x, Int(10))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= x 10))\n"
        "(assert (= 1 1))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == bound
    assert asserts[1].is_true()


def test_field_bounds_0_and_p_are_not_eliminated():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    lower = LE(Int(0), x)
    upper = LT(x, Int(p))
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        f"(assert (< x {p}))\n"
        "(check-sat)\n"
    )
    assert asserts[0] == lower
    assert asserts[1] == upper


def test_simplify_intervals_can_append_derived_ranges():
    x = Symbol("x", INT)
    expected_range = And(LE(Int(0), x), LE(x, Int(10)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= 0 x))\n"
        "(assert (<= x 10))\n"
        "(assert (= 1 1))\n"
        "(check-sat)\n"
    )
    assert asserts[2].is_true()
    assert any(c == expected_range for c in asserts)


def test_fixed_point_opcode_flags_sum_forces_all_zero():
    sub = Symbol("sub", INT)
    xor = Symbol("xor", INT)
    orf = Symbol("orf", INT)
    andf = Symbol("andf", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun sub () Int)\n"
        "(declare-fun xor () Int)\n"
        "(declare-fun orf () Int)\n"
        "(declare-fun andf () Int)\n"
        "(assert (or (= sub 0) (= sub 1)))\n"
        "(assert (or (= xor 0) (= xor 1)))\n"
        "(assert (or (= orf 0) (= orf 1)))\n"
        "(assert (or (= andf 0) (= andf 1)))\n"
        "(assert (= (+ sub (* 2 xor) (* 3 orf) (* 4 andf)) 0))\n"
        "(check-sat)\n"
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
        f"(set-logic ALL)\n"
        "(declare-fun sub2 () Int)\n"
        "(declare-fun xor2 () Int)\n"
        "(declare-fun orf2 () Int)\n"
        "(declare-fun andf2 () Int)\n"
        "(assert (or (= sub2 0) (= sub2 1)))\n"
        "(assert (or (= xor2 0) (= xor2 1)))\n"
        "(assert (or (= orf2 0) (= orf2 1)))\n"
        "(assert (or (= andf2 0) (= andf2 1)))\n"
        f"(assert (= (mod (+ sub2 (* 2 xor2) (* 3 orf2) (* 4 andf2)) {p}) 0))\n"
        "(check-sat)\n"
    )
    assert any(a == Equals(sub, Int(0)) for a in asserts)
    assert any(a == Equals(xor, Int(0)) for a in asserts)
    assert any(a == Equals(orf, Int(0)) for a in asserts)
    assert any(a == Equals(andf, Int(0)) for a in asserts)


def test_mod_zero_rewrites_to_unique_nonzero_multiple():
    p = int(ARGS().field_type.value)
    x = Symbol("x_unique_mult", INT)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun x_unique_mult () Int)\n"
        f"(assert (<= {p - 2} x_unique_mult))\n"
        f"(assert (<= x_unique_mult {p + 3}))\n"
        f"(assert (= (mod x_unique_mult {p}) 0))\n"
        "(check-sat)\n"
    )
    assert any(a == Equals(x, Int(p)) for a in asserts)


def test_constraints_5_and_6_style_mods_are_removed():
    p = int(ARGS().field_type.value)
    asserts = _asserts_from_script(
        f"(set-logic ALL)\n"
        "(declare-fun f0 () Int)\n"
        "(declare-fun f1 () Int)\n"
        "(declare-fun f2 () Int)\n"
        "(declare-fun f3 () Int)\n"
        "(assert (or (= f0 0) (= f0 1) (= f0 2)))\n"
        "(assert (or (= f1 0) (= f1 1) (= f1 2)))\n"
        "(assert (or (= f2 0) (= f2 1) (= f2 2)))\n"
        "(assert (or (= f3 0) (= f3 1) (= f3 2)))\n"
        f"(assert (or (= (+ f0 f1 f2 f3) 0) (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0) (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))\n"
        f"(assert (or (= (mod (+ {p - 2} (+ f0 f1 f2 f3)) {p}) 0) (= (mod (+ {p - 1} (+ f0 f1 f2 f3)) {p}) 0)))\n"
        "(check-sat)\n"
    )
    assert all(not _has_mod(f) for f in asserts)


def test_derived_multi_interval_constraint_is_disjunction():
    x = Symbol("x_disj_domain", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun x_disj_domain () Int)\n"
        "(assert (or (= x_disj_domain 0) (= x_disj_domain 1)))\n"
        "(assert true)\n"
        "(check-sat)\n"
    )
    expected = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    assert any(c == expected for c in asserts)


def test_exists_quantifier_injects_bounds_with_conjunction():
    x = Symbol("x_exists_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(assert (exists ((x_exists_inject Int)) (or (= x_exists_inject 0) (= x_exists_inject 1))))\n"
        "(check-sat)\n"
    )
    out = asserts[0]
    assert out.is_exists()
    injected = out.arg(0)
    assert injected.is_and()
    assert body in injected.args()
    assert Or(Equals(x, Int(0)), Equals(x, Int(1))) in injected.args()


def test_forall_quantifier_injects_bounds_with_implication_guard():
    x = Symbol("x_forall_inject", INT)
    body = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(assert (forall ((x_forall_inject Int)) (or (= x_forall_inject 0) (= x_forall_inject 1))))\n"
        "(check-sat)\n"
    )
    out = asserts[0]
    assert out.is_forall()
    injected = out.arg(0)
    assert injected.is_implies()
    assert injected.arg(0) == Or(Equals(x, Int(0)), Equals(x, Int(1)))
    assert injected.arg(1) == body


def test_quantifier_injection_only_uses_variables_present_in_body():
    y = Symbol("y_quant_scope", INT)
    asserts = _asserts_from_script(
        "(set-logic ALL)\n"
        "(declare-fun y_quant_scope () Int)\n"
        "(assert (= y_quant_scope 7))\n"
        "(assert (forall ((x_quant_scope Int)) (= x_quant_scope x_quant_scope)))\n"
        "(check-sat)\n"
    )
    out = asserts[1]
    # y is not present in quantifier body, so no bound for y may be injected there.
    assert y not in out.get_free_variables()
