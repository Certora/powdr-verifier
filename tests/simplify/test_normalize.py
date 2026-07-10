from io import StringIO
from textwrap import dedent

from src.simplify.normalize import collect_variables, relation_poly_diff, simplify_normalize
from src.smt.utils import *  # noqa: F401,F403 - monkeypatches pysmt (MOD support) before shortcuts
from src.utils.args import ARGS

# Imported after ``src.smt.utils`` on purpose: that ``import *`` installs the
# backend MOD operator; importing ``pysmt.shortcuts`` earlier breaks it.
from pysmt.shortcuts import Iff, Not, Solver


def _parse(s: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(s).strip() + "\n"))


def _satisfiable(formula: FNode) -> bool:
    with Solver(name="z3", logic=None) as s:
        s.add_assertion(formula)
        return s.solve()


def _equivalent(f: FNode, g: FNode) -> bool:
    """True iff ``f <=> g`` is valid (``Not(Iff(f, g))`` is unsat)."""
    with Solver(name="z3", logic=None) as s:
        s.add_assertion(Not(Iff(f, g)))
        return not s.solve()


def test_normalize_field_monic_scales_coeffs():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mod (+ (* 2 x) (* 4 y)) {p}) 0))
        (check-sat)
        """
    )
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(x, Times(Int(2), y)))]


def test_normalize_orders_terms_grlex():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mod (+ y x) {p}) 0))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(Symbol("x", INT), Symbol("y", INT)))]


def test_normalize_a_minus_b_shape():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= (mod (+ (* 3 x) 6) {p}) 0))
        (check-sat)
        """
    )
    x = Symbol("x", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(x, Int(2)))]


def test_normalize_field_monic_2x_plus_3y():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mod (+ (* 2 x) (* 3 y)) {p}) 0))
        (check-sat)
        """
    )
    coef_y = (3 * pow(2, -1, p)) % p
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(x, Times(Int(coef_y), y)))]


def test_normalize_mod_vs_mod_same_congruence_class():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= (mod (+ (* 3 x) 6) {p}) (mod (* 3 (+ x 2)) {p})))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Int(0))]


def test_normalize_mod_vs_mod_difference():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mod (+ (* 2 x) (* 4 y)) {p}) (mod x {p})))
        (check-sat)
        """
    )
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(x, Times(Int(4), y)))]


def test_normalize_zero_vs_field_mod():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= 0 (mod (+ (* 2 x) (* 4 y)) {p})))
        (check-sat)
        """
    )
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [field_eq(Plus(x, Times(Int(2), y)))]


def test_normalize_zero_equals_zero():
    smt = _parse(
        """
        (set-logic ALL)
        (assert (= 0 0))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Int(0), Int(0))]


def test_normalize_opaque_uf_term_is_a_generator():
    # Atoms carrying an uninterpreted (bitwise-like) Int term must be normalized, not skipped:
    # the opaque ``uf(a, 3)`` application is treated as an atomic ring generator.
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun a () Int)
        (declare-fun uf (Int Int) Int)
        (assert (= (mod (+ (* 256 x) (* 7864320 (uf a 3))) {p}) 0))
        (check-sat)
        """
    )
    old = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    new = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    # The pass must have rewritten the atom rather than bailing on the ``uf`` term.
    assert new != old


def test_normalize_uf_reflection_collapses_to_same_monic():
    # The booleanity-reflection bug: two atoms that are unit-(-1) multiples of each other,
    # both containing an opaque ``uf`` term, must collapse to one canonical monic form.
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun a () Int)
        (declare-fun uf (Int Int) Int)
        (assert (= (mod (+ (* 256 x) (* 7864320 (uf a 3))) {p}) 0))
        (assert (= (mod (+ (* {p - 256} x) (* {(p - 7864320) % p} (uf a 3))) {p}) 0))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    # ``L ≡ 0`` and ``-L ≡ 0`` normalize to the identical monic representative.
    assert asserts[0] == asserts[1]


def test_normalize_uf_booleanity_roots_reflect():
    # Mirrors 036↔037: root ``V-1`` (before) and its reflection ``-V+1`` (after) unify.
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun a () Int)
        (declare-fun uf (Int Int) Int)
        (assert (= (mod (+ (* 256 x) (* 7864320 (uf a 3)) {p - 1}) {p}) 0))
        (assert (= (mod (+ (* {p - 256} x) (* {(p - 7864320) % p} (uf a 3)) 1) {p}) 0))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts[0] == asserts[1]


def test_normalize_skips_mod():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= (mod x 7) 0))
        (check-sat)
        """
    )
    old = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    new = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    assert old.serialize() == new.serialize()


def test_normalize_weak_eq_orders_terms_grlex():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (+ y x) (+ x y)))
        (check-sat)
        """
    )
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Int(0), Int(0))]


def test_normalize_weak_eq_divides_coeff_gcd():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (+ (* 2 x) (* 4 y)) 0))
        (check-sat)
        """
    )
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Plus(x, Times(Int(2), y)), Int(0))]


def test_normalize_weak_lt_moves_to_diff():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (< (+ y x) x))
        (check-sat)
        """
    )
    y = Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [LT(y, Int(0))]


def test_normalize_weak_le_moves_to_diff():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= (+ (* 2 x) y) x))
        (check-sat)
        """
    )
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [LE(Plus(x, y), Int(0))]


def test_normalize_weak_le_field_mod_vs_const_left_intact():
    # (mod (x+y) P) <= 255 is a range check. Field reduction (mod P) preserves
    # "= 0" but NOT order, so normalize must leave modular inequalities intact.
    # The old code rewrote this to LE(wrap_mod(x+y-255), 0), i.e. the *equality*
    # x+y == 255 (mod P) -- unsound (turned "<= 255" into "= 255").
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (<= (mod (+ y x) {p}) 255))
        (check-sat)
        """
    )
    original = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [original]  # declined -> unchanged
    x, y = Symbol("x", INT), Symbol("y", INT)
    buggy = LE(wrap_mod(Plus(x, y, Int((-255) % p))), Int(0))
    assert not _equivalent(original, buggy)  # the old rewrite was not equivalent


def test_normalize_weak_lt_both_field_mod_left_intact():
    # (mod (y+x) P) < (mod x P): a genuine modular comparison. The old code
    # rewrote it to the always-false (mod y P) < 0 -- the guest-keccak
    # 2102932 034->035 vacuous-unsat bug. Must be left intact.
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (< (mod (+ y x) {p}) (mod x {p})))
        (check-sat)
        """
    )
    original = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [original]  # declined -> unchanged
    assert _satisfiable(asserts[0])  # not vacuous
    buggy = LT(wrap_mod(Symbol("y", INT)), Int(0))
    assert not _satisfiable(buggy)  # the old form was always-false


def test_normalize_modular_lt_not_vacuous():
    # Regression for the timestamp IsLessThan comparison that made
    # guest-keccak 2102932 034->035 vacuously unsat: (mod (a+1) P) < (mod b P)
    # must stay satisfiable and equivalent to the input -- never collapse to
    # the always-false (mod (a-b+1) P) < 0.
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (< (mod (+ a 1) {p}) (mod b {p})))
        (check-sat)
        """
    )
    original = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert _satisfiable(asserts[0])
    assert _equivalent(asserts[0], original)


def test_normalize_nonmodular_lt_preserves_sign():
    # (3x < 5x) <=> x > 0. The gcd rescale negates when the leading coeff is
    # negative (diff = -2x); for an inequality that flips the relation to the
    # unsound x < 0. Sign must be preserved on the non-modular path.
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (< (* 3 x) (* 5 x)))
        (check-sat)
        """
    )
    original = [c.args[0] for c in smt.commands if c.name == "assert"][0]
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert _equivalent(asserts[0], original)
    # the would-be sign-flipped form must NOT be equivalent
    assert not _equivalent(asserts[0], LT(Symbol("x", INT), Int(0)))


def test_relation_poly_diff_plain_eq():
    smt = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (+ y x) (+ x y)))
        (check-sat)
        """
    )
    vars_ = collect_variables(smt)
    vi = {s: i for i, s in enumerate(vars_)}
    lhs, rhs = [c.args[0] for c in smt.commands if c.name == "assert"][0].args()
    parsed = relation_poly_diff(lhs, rhs, vi, vars_)
    assert parsed == ({}, False)


def test_relation_poly_diff_field_mod_eq():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mod (+ (* 2 x) (* 4 y)) {p}) 0))
        (check-sat)
        """
    )
    vars_ = collect_variables(smt)
    vi = {s: i for i, s in enumerate(vars_)}
    lhs, rhs = [c.args[0] for c in smt.commands if c.name == "assert"][0].args()
    parsed = relation_poly_diff(lhs, rhs, vi, vars_)
    assert parsed is not None
    diff, modular = parsed
    assert modular is True
    x, y = Symbol("x", INT), Symbol("y", INT)
    assert diff == _poly_from_terms(vars_, (x, 2), (y, 4), mod=p)


def test_relation_poly_diff_mod_vs_const():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (<= (mod x {p}) 255))
        (check-sat)
        """
    )
    vars_ = collect_variables(smt)
    vi = {s: i for i, s in enumerate(vars_)}
    lhs, rhs = [c.args[0] for c in smt.commands if c.name == "assert"][0].args()
    parsed = relation_poly_diff(lhs, rhs, vi, vars_)
    assert parsed is not None
    diff, modular = parsed
    assert modular is True
    x = Symbol("x", INT)
    assert diff == _poly_from_terms(vars_, (x, 1), mod=p, const=-255 % p)


def test_relation_poly_diff_mixed_mod_plain_rejected():
    p = int(ARGS().field_type.value)
    smt = _parse(
        f"""
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (< (mod x {p}) y))
        (check-sat)
        """
    )
    vars_ = collect_variables(smt)
    vi = {s: i for i, s in enumerate(vars_)}
    lhs, rhs = [c.args[0] for c in smt.commands if c.name == "assert"][0].args()
    assert relation_poly_diff(lhs, rhs, vi, vars_) is None


def _poly_from_terms(
    vars_: tuple,
    *terms: tuple,
    mod: int | None = None,
    const: int = 0,
) -> dict:
    idx = {v: i for i, v in enumerate(vars_)}
    poly: dict = {}
    for sym, coef in terms:
        poly[(idx[sym],)] = coef % mod if mod is not None else coef
    if const:
        c = const % mod if mod is not None else const
        if c:
            poly[()] = c
    return poly
