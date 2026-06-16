from io import StringIO
from textwrap import dedent

from src.simplify.normalize import simplify_normalize
from src.smt.utils import *
from src.utils.args import ARGS


def _parse(s: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(s).strip() + "\n"))


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
    assert asserts == [field_eq(Int(0))]


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
