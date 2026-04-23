from io import StringIO
from textwrap import dedent

from src.simplify.demod import simplify_demod
from src.smt.utils import *


def test_demod_uses_top_level_bounds_across_asserts():
    p = int(ARGS().field_type.value)
    parser = SmtLibParser()
    smt_script = parser.get_script(
        StringIO(
            dedent(
                f"""
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= 0 x))
                (assert (< x {p}))
                (assert (= (mod x {p}) 0))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_demod(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)

    assert LE(Int(0), x) in asserts
    assert LT(x, Int(p)) in asserts
    assert Equals(x, Int(0)) in asserts


def test_demod_learns_from_self_mod_equality():
    p = int(ARGS().field_type.value)
    parser = SmtLibParser()
    smt_script = parser.get_script(
        StringIO(
            dedent(
                f"""
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (= x (mod x {p})))
                (assert (= (mod x {p}) 7))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_demod(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)

    assert Equals(x, Mod(x, Int(p))) in asserts
    assert Equals(x, Int(7)) in asserts


def test_demod_does_not_eliminate_without_upper_bound():
    p = int(ARGS().field_type.value)
    parser = SmtLibParser()
    smt_script = parser.get_script(
        StringIO(
            dedent(
                f"""
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= 0 x))
                (assert (= (mod x {p}) 0))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_demod(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert Equals(Mod(Symbol("x", INT), Int(p)), Int(0)) in asserts


def test_demod_uses_actual_modulus_not_field_modulus():
    parser = SmtLibParser()
    smt_script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (declare-fun x () Int)
                (assert (<= 0 x))
                (assert (< x 17))
                (assert (= (mod x 17) 3))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_demod(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert Equals(Symbol("x", INT), Int(3)) in asserts


def test_demod_folds_mod_of_two_constants():
    parser = SmtLibParser()
    smt_script = parser.get_script(
        StringIO(
            dedent(
                """
                (set-logic ALL)
                (assert (= (mod 17 5) 2))
                (check-sat)
                """
            ).strip()
            + "\n"
        )
    )

    simplified = simplify_demod(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert Equals(Int(2), Int(2)) in asserts
