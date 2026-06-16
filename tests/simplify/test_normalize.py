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
    pm = Int(p)
    zmod = Mod(Int(0), pm)
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Mod(Plus(x, Times(Int(2), y)), pm), zmod)]


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
    pm = Int(p)
    zmod = Mod(Int(0), pm)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Mod(Plus(Symbol("x", INT), Symbol("y", INT)), pm), zmod)]


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
    pm = Int(p)
    zmod = Mod(Int(0), pm)
    x = Symbol("x", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Mod(Plus(x, Int(2)), pm), zmod)]


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
    pm = Int(p)
    zmod = Mod(Int(0), pm)
    coef_y = (3 * pow(2, -1, p)) % p
    x, y = Symbol("x", INT), Symbol("y", INT)
    simplify_normalize(smt)
    asserts = [c.args[0] for c in smt.commands if c.name == "assert"]
    assert asserts == [Equals(Mod(Plus(x, Times(Int(coef_y), y)), pm), zmod)]


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
