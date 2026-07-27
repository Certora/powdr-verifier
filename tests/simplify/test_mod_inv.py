from io import StringIO
from textwrap import dedent

from src.simplify.mod_inv import UF_MOD_INV, simplify_mod_inv
from src.smt.utils import *


def _parse(script_text: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(script_text).strip() + "\n"))


def test_mod_inv_replaces_uf_call_with_fresh_symbol_and_adds_constraint():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_mod_inv (Int) Int)
        (declare-fun x () Int)
        (assert (= (uf_mod_inv x) 7))
        (check-sat)
        """
    )

    simplified = simplify_mod_inv(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    declares = [cmd.args[0] for cmd in simplified if cmd.name == "declare-fun"]
    assert len(asserts) == 2
    main = asserts[0]
    side = asserts[1]
    assert main.is_equals()
    fresh = main.arg(0) if main.arg(0).is_symbol() else main.arg(1)
    assert fresh.symbol_name().startswith("__mod_inv_")
    assert fresh in declares
    # The fallback inverse axiom is guarded: the inverse is undefined at 0, so
    # `fresh * T ≡ 1` is asserted only under `T ≠ 0` (else it would force T ≠ 0).
    assert side == Implies(
        Not(Equals(wrap_mod(Symbol("x", INT)), Int(0))),
        Equals(wrap_mod(Times(fresh, Symbol("x", INT))), Int(1)),
    )


def test_mod_inv_is_noop_without_uf_mod_inv_terms():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_mod_inv (Int) Int)
        (declare-fun x () Int)
        (assert (= x 1))
        (check-sat)
        """
    )

    simplified = simplify_mod_inv(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert len(asserts) == 1


def test_mod_inv_creates_distinct_fresh_symbols():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_mod_inv (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (+ (uf_mod_inv x) (uf_mod_inv y)) 0))
        (check-sat)
        """
    )

    simplified = simplify_mod_inv(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    declares = [cmd.args[0] for cmd in simplified if cmd.name == "declare-fun"]
    assert len(asserts) == 3
    main = asserts[0]
    assert main.is_equals()
    lhs = main.arg(0) if main.arg(0).is_plus() else main.arg(1)
    s1, s2 = lhs.args()
    assert s1 != s2
    assert s1.symbol_name().startswith("__mod_inv_")
    assert s2.symbol_name().startswith("__mod_inv_")
    inv_x = Implies(Not(Equals(wrap_mod(Symbol("x", INT)), Int(0))),
                    Equals(wrap_mod(Times(s1, Symbol("x", INT))), Int(1)))
    inv_y = Implies(Not(Equals(wrap_mod(Symbol("y", INT)), Int(0))),
                    Equals(wrap_mod(Times(s2, Symbol("y", INT))), Int(1)))
    assert asserts[1] in (inv_x, inv_y)
    assert asserts[2] in (inv_x, inv_y)
    assert asserts[1] != asserts[2]
    assert s1 in declares
    assert s2 in declares


def test_mod_inv_does_not_rewrite_inside_quantifier():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_mod_inv (Int) Int)
        (declare-fun y () Int)
        (assert (forall ((x Int)) (= (uf_mod_inv x) y)))
        (check-sat)
        """
    )

    simplified = simplify_mod_inv(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert len(asserts) == 1
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    expected = ForAll([x], Equals(Function(UF_MOD_INV, [x]), y))
    assert asserts[0] == expected
