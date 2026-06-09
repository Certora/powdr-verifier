from io import StringIO
from textwrap import dedent

from src.simplify.bitwise import UF_AND, UF_OR, UF_XOR, simplify_gbitwise, simplify_qbitwise
from src.smt.utils import *


def _parse(script_text: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(script_text).strip() + "\n"))


def test_qbitwise_inserts_quantified_axioms_when_uf_xor_is_used():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (= (uf_xor x y) z))
        (check-sat)
        """
    )

    simplified = simplify_qbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("__bwx", INT)
    y = Symbol("__bwy", INT)

    assert ForAll([x], Equals(Function(UF_XOR, [x, Int(0)]), x)) in asserts
    assert ForAll([x], Equals(Function(UF_XOR, [Int(0), x]), x)) in asserts
    assert ForAll([x], Equals(Function(UF_XOR, [x, x]), Int(0))) in asserts
    assert ForAll(
        [x, y],
        Implies(Equals(Function(UF_XOR, [x, y]), x), Equals(y, Int(0))),
    ) in asserts
    assert ForAll(
        [x, y],
        Implies(Equals(Function(UF_XOR, [y, x]), x), Equals(y, Int(0))),
    ) in asserts


def test_qbitwise_is_noop_without_uf_xor_terms():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun x () Int)
        (assert (= x 7))
        (check-sat)
        """
    )

    simplified = simplify_qbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert asserts == [Equals(Symbol("x", INT), Int(7))]


def test_gbitwise_grounds_axioms_for_seen_terms():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (= (uf_xor x y) z))
        (assert (= (uf_xor x x) 0))
        (check-sat)
        """
    )

    simplified = simplify_gbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    z = Symbol("z", INT)
    xy = Function(UF_XOR, [x, y])

    assert Iff(Equals(x, y), Equals(xy, Int(0))) in asserts
    assert Iff(Equals(x, Int(0)), Equals(xy, y)) in asserts
    assert Iff(Equals(y, Int(0)), Equals(xy, x)) in asserts
    assert Iff(Equals(x, xy), Equals(y, Int(0))) in asserts
    assert Iff(Equals(y, xy), Equals(x, Int(0))) in asserts
    assert Equals(Int(0), Int(0)) in asserts
    assert Equals(xy, z) in asserts


def test_gbitwise_injects_axioms_inside_quantifier():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (forall ((x Int)) (= (uf_xor x y) z)))
        (check-sat)
        """
    )

    simplified = simplify_gbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    z = Symbol("z", INT)
    xy = Function(UF_XOR, [x, y])

    assert len(asserts) == 1
    assert asserts[0].is_forall()
    body = asserts[0].arg(0)
    assert body.is_and()
    assert Equals(xy, z) in body.args()
    assert Iff(Equals(x, y), Equals(xy, Int(0))) in body.args()
    assert Iff(Equals(x, Int(0)), Equals(xy, y)) in body.args()
    assert Iff(Equals(y, Int(0)), Equals(xy, x)) in body.args()
    assert Iff(Equals(x, xy), Equals(y, Int(0))) in body.args()
    assert Iff(Equals(y, xy), Equals(x, Int(0))) in body.args()


def test_qbitwise_injects_axioms_inside_quantifier():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (forall ((x Int)) (= (uf_xor x y) z)))
        (check-sat)
        """
    )

    simplified = simplify_qbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    z = Symbol("z", INT)
    qx = Symbol("__bwx", INT)
    qy = Symbol("__bwy", INT)

    assert len(asserts) == 1
    assert asserts[0].is_forall()
    body = asserts[0].arg(0)
    assert body.is_and()
    assert Equals(Function(UF_XOR, [x, y]), z) in body.args()
    assert ForAll([qx], Equals(Function(UF_XOR, [qx, Int(0)]), qx)) in body.args()
    assert ForAll([qx], Equals(Function(UF_XOR, [Int(0), qx]), qx)) in body.args()
    assert ForAll([qx], Equals(Function(UF_XOR, [qx, qx]), Int(0))) in body.args()
    assert ForAll(
        [qx, qy],
        Implies(Equals(Function(UF_XOR, [qx, qy]), qx), Equals(qy, Int(0))),
    ) in body.args()
    assert ForAll(
        [qx, qy],
        Implies(Equals(Function(UF_XOR, [qy, qx]), qx), Equals(qy, Int(0))),
    ) in body.args()


def test_gbitwise_simplifies_quantified_xor_terms_locally():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (assert (forall ((x Int)) (= (uf_xor x 0) x)))
        (assert (forall ((x Int)) (= (uf_xor 0 x) x)))
        (assert (forall ((x Int)) (= (uf_xor x x) 0)))
        (check-sat)
        """
    )

    simplified = simplify_gbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)

    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(Int(0), Int(0))) in asserts


def test_qbitwise_inserts_andor_connection_without_xor():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_and (Int Int) Int)
        (declare-fun uf_or (Int Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (uf_and x y) 0))
        (check-sat)
        """
    )
    simplified = simplify_qbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("__bw_andor_x", INT)
    y = Symbol("__bw_andor_y", INT)
    expected = ForAll(
        [x, y],
        Equals(
            Function(UF_OR, [x, y]),
            Minus(Plus(x, y), Function(UF_AND, [x, y])),
        ),
    )
    assert expected in asserts


def test_gbitwise_inserts_grounded_andor_and_connection():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_and (Int Int) Int)
        (declare-fun uf_or (Int Int) Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (= (uf_or a b) 7))
        (check-sat)
        """
    )
    simplified = simplify_gbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    assert Equals(
        Function(UF_OR, [a, b]),
        Minus(Plus(a, b), Function(UF_AND, [a, b])),
    ) in asserts


def test_qbitwise_simplifies_quantified_xor_terms_locally():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (assert (forall ((x Int)) (= (uf_xor x 0) x)))
        (assert (forall ((x Int)) (= (uf_xor 0 x) x)))
        (assert (forall ((x Int)) (= (uf_xor x x) 0)))
        (check-sat)
        """
    )

    simplified = simplify_qbitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)

    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(Int(0), Int(0))) in asserts
