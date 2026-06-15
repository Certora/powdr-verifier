from io import StringIO
from textwrap import dedent

import z3

from src.simplify.bitwise import UF_AND, UF_OR, UF_XOR, simplify_bitwise
from src.smt.utils import *

BABYBEAR_PRIME = 0x78000001


def _parse(script_text: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(script_text).strip() + "\n"))


def test_bitwise_is_noop_without_bitwise_uf():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun x () Int)
        (assert (= x 7))
        (check-sat)
        """
    )

    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]

    assert asserts == [Equals(Symbol("x", INT), Int(7))]


def test_bitwise_grounds_axioms_for_seen_terms():
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

    simplified = simplify_bitwise(smt_script)
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


def test_bitwise_injects_axioms_inside_quantifier():
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

    simplified = simplify_bitwise(smt_script)
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


def test_bitwise_simplifies_quantified_xor_terms_locally():
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

    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)

    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(x, x)) in asserts
    assert ForAll([x], Equals(Int(0), Int(0))) in asserts


def test_bitwise_inserts_andor_connection_from_and_only():
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
    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    assert Equals(
        Function(UF_OR, [x, y]),
        Minus(Plus(x, y), Function(UF_AND, [x, y])),
    ) in asserts


def test_bitwise_inserts_grounded_andor_and_connection():
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
    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    assert Equals(
        Function(UF_OR, [a, b]),
        Minus(Plus(a, b), Function(UF_AND, [a, b])),
    ) in asserts


def test_bitwise_emits_symmetric_keystone_for_xor_term():
    """The keystone x+y = uf_xor + 2·uf_and (byte-guarded) is attached to every
    uf_xor application — independent of the AND/OR recognizer — so the AND/OR
    byte-range is present on both sides of a VC. Regression for 2105476
    002->003, whose multiplexed (pre-solver) side the recognizer cannot lift."""
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
    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    x, y = Symbol("x", INT), Symbol("y", INT)
    xy = Function(UF_XOR, [x, y])
    conj = Function(UF_AND, [x, y])
    guard = And(LE(Int(0), x), LE(x, Int(255)), LE(Int(0), y), LE(y, Int(255)))
    assert Implies(guard, Equals(Plus(x, y), Plus(xy, Times(Int(2), conj)))) in asserts
    assert Implies(guard, And(LE(Int(0), conj), LE(conj, x), LE(conj, y))) in asserts


def test_bitwise_keystone_skipped_for_equal_args():
    """uf_xor(x,x) folds to 0; no keystone (guarded Implies) is emitted."""
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun uf_xor (Int Int) Int)
        (declare-fun x () Int)
        (assert (= (uf_xor x x) 0))
        (check-sat)
        """
    )
    simplified = simplify_bitwise(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert not any(a.is_implies() for a in asserts)


def _z3_and_row(a_value):
    """z3 fixtures for a BabyBear AND row a = (x & y) via the XOR table.
    Operands x=2,y=1 (real a=0). Table arg z = (x+y-2a) mod p; uf_xor(x,y)=z.
    Returns (solver, uf_xor, x, y) so a test can add the keystone."""
    p = BABYBEAR_PRIME
    x, y = 2, 1
    z = (x + y - 2 * a_value) % p
    uf_xor = z3.Function("uf_xor", z3.IntSort(), z3.IntSort(), z3.IntSort())
    uf_and = z3.Function("uf_and", z3.IntSort(), z3.IntSort(), z3.IntSort())
    s = z3.Solver()
    s.add(0 <= x, x <= 255, 0 <= y, y <= 255, 0 <= z, z <= 255)
    s.add(uf_xor(x, y) == z)
    return s, uf_xor, uf_and, x, y


def test_keystone_rejects_overapproximated_and_witness():
    """Bogus a=(p-1)/2 makes the wrapped table arg z=4 (solver wants uf_xor(2,1)=4).
    Keystone 2+1 = uf_xor + 2·uf_and then forces 2·uf_and=-1 — unsat over Int."""
    s, uf_xor, uf_and, x, y = _z3_and_row((BABYBEAR_PRIME - 1) // 2)
    assert s.check() == z3.sat  # over-approximated model exists pre-keystone
    s.add(x + y == uf_xor(x, y) + 2 * uf_and(x, y))
    assert s.check() == z3.unsat


def test_keystone_admits_real_and_witness():
    """Real a=2&1=0 gives z=3=2^1; keystone pins uf_and(2,1)=0 and stays sat."""
    s, uf_xor, uf_and, x, y = _z3_and_row(0)
    s.add(x + y == uf_xor(x, y) + 2 * uf_and(x, y))
    s.add(0 <= uf_and(x, y), uf_and(x, y) <= x, uf_and(x, y) <= y)
    assert s.check() == z3.sat
    assert s.model().eval(uf_and(x, y)).as_long() == 0
