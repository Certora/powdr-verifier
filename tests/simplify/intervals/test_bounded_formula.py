"""Unit tests for `BoundedFormula`."""

import pytest
from pysmt.typing import INT

from src.simplify.intervals.bounded_formula import BoundedFormula
from src.simplify.intervals.domain import IntDomain, IntInterval, IntVarDomains
from src.smt.utils import *


def test_constructor_mirrors_args_and_starts_top_domains():
    f = And(Bool(True), Bool(False))
    b = BoundedFormula(f)
    assert b.formula is f
    assert b.domains.is_top()
    assert len(b.subformulas) == 2
    assert b.subformulas[0].formula is f.args()[0]
    assert b.subformulas[1].formula is f.args()[1]
    assert b.subformulas[0].domains.is_top()
    assert b.subformulas[0].subformulas == []


def test_constructor_leaf_has_no_subformulas():
    b = BoundedFormula(Int(7))
    assert b.subformulas == []
    assert b.formula.is_int_constant()


def test_constructor_equals_not_unpacked():
    e = Equals(Int(1), Int(1))
    b = BoundedFormula(e)
    assert b.subformulas == []
    assert b.formula is e


def test_as_fnode_leaf_returns_original_formula():
    c = Int(7)
    b = BoundedFormula(c)
    assert b.as_fnode() is c


def test_as_fnode_raises_when_subformula_count_mismatches_args():
    f = And(Bool(True), Bool(False))
    b = BoundedFormula(f)
    b.subformulas.pop()
    with pytest.raises(ValueError, match="subformula count"):
        b.as_fnode()


def test_as_fnode_and_roundtrip():
    f = And(Bool(True), Equals(Int(1), Int(1)))
    b = BoundedFormula(f)
    out = b.as_fnode()
    assert out.is_and()
    assert len(list(out.args())) == 2


def test_as_fnode_or_rebuilds_node_type():
    f = Or(Bool(False), Bool(True))
    b = BoundedFormula(f)
    out = b.as_fnode()
    assert out.is_or()
    assert len(list(out.args())) == 2


def test_as_fnode_and_injects_domain_constraints():
    x = Symbol("bx", INT)
    f = And(Equals(x, Int(0)), Bool(True))
    b = BoundedFormula(f)
    b.domains = IntVarDomains({x: IntDomain.from_interval(IntInterval(0, 5))})
    out = b.as_fnode()
    assert out.is_and()
    assert len(list(out.args())) == 3


def test_as_fnode_and_top_domains_no_extra_conjuncts_from_domains():
    f = And(Bool(True), Bool(False))
    b = BoundedFormula(f)
    assert b.domains.is_top()
    out = b.as_fnode()
    assert out.is_and()
    assert len(list(out.args())) == 2


def test_as_fnode_roundtrip_mixed_bool_arith_quantifier():
    """ForAll over a body with implies, conjunction, disjunction, negation, and int relations."""
    x = Symbol("qx", INT)
    inner = And(
        Or(Not(LE(x, Int(0))), Equals(x, Int(1))),
        LE(Int(0), x),
    )
    f = ForAll([x], Implies(LT(Int(0), x), inner))
    assert BoundedFormula(f).as_fnode() == f


def test_refine_domains_le_leaf():
    x = Symbol("rx", INT)
    f = LE(x, Int(10))
    b = BoundedFormula(f)
    assert b.domains.is_top()
    assert b.refine_domains() is True
    d = b.domains.get(x)
    assert not d.is_top()
    assert d.hull().hi is not None and d.hull().hi <= 10
    assert b.refine_domains() is False


def test_refine_domains_does_not_visit_children_under_and():
    x = Symbol("sx", INT)
    inner_le = LE(x, Int(3))
    inner_eq = Equals(x, Int(1))
    f = And(inner_le, inner_eq)
    b = BoundedFormula(f)
    le_bf = next(s for s in b.subformulas if s.formula is inner_le)
    eq_bf = next(s for s in b.subformulas if s.formula is inner_eq)
    assert b.refine_domains() is False
    assert b.domains.is_top()
    assert le_bf.domains.is_top()
    assert eq_bf.domains.is_top()


def test_refine_domains_noop_on_bool_op_root_without_children():
    b = BoundedFormula(And())
    assert b.refine_domains() is False
    assert b.domains.is_top()


def test_push_down_leaf_returns_false():
    x = Symbol("pd_leaf", INT)
    b = BoundedFormula(LE(x, Int(1)))
    assert b.push_down() is False


def test_push_down_intersects_children_domains():
    x = Symbol("px", INT)
    f = And(Bool(True), Bool(True))
    b = BoundedFormula(f)
    dom = IntDomain.from_interval(IntInterval(0, 5))
    b.domains = IntVarDomains({x: dom})
    assert b.push_down() is True
    for sub in b.subformulas:
        assert sub.domains.get(x) == dom
    assert b.push_down() is False


def test_lift_up_leaf_returns_false():
    x = Symbol("lu_leaf", INT)
    b = BoundedFormula(LE(x, Int(1)))
    assert b.lift_up() is False


def test_lift_up_and_intersects_children_then_meets_parent():
    x = Symbol("lx", INT)
    f = And(Bool(True), Bool(True))
    b = BoundedFormula(f)
    d0 = IntDomain.from_interval(IntInterval(0, 5))
    d1 = IntDomain.from_interval(IntInterval(2, 8))
    b.subformulas[0].domains = IntVarDomains({x: d0})
    b.subformulas[1].domains = IntVarDomains({x: d1})
    assert b.lift_up() is True
    assert b.domains.get(x) == d0.intersect(d1)
    assert b.lift_up() is False


def test_lift_up_or_unions_children_then_meets_parent():
    x = Symbol("lox", INT)
    f = Or(Bool(True), Bool(True))
    b = BoundedFormula(f)
    d0 = IntDomain.from_interval(IntInterval(0, 1))
    d1 = IntDomain.from_interval(IntInterval(2, 3))
    b.subformulas[0].domains = IntVarDomains({x: d0})
    b.subformulas[1].domains = IntVarDomains({x: d1})
    assert b.lift_up() is True
    assert b.domains.get(x) == IntDomain.from_interval(d0.union(d1).hull())
    assert b.lift_up() is False


def test_lift_up_and_top_conjunct_does_not_erase_refinement():
    x = Symbol("lsx", INT)
    f = And(Bool(True), Bool(True))
    b = BoundedFormula(f)
    d = IntDomain.from_interval(IntInterval(0, 5))
    b.subformulas[0].domains = IntVarDomains({x: d})
    assert b.subformulas[1].domains.is_top()
    assert b.lift_up() is True
    assert b.domains.get(x) == d
    assert b.lift_up() is False


def test_lift_up_non_and_or_bool_op_is_noop():
    b = BoundedFormula(Not(Bool(False)))
    assert b.lift_up() is False
    assert b.domains.is_top()


def test_refine_recursive_leaf_same_as_refine_domains():
    x = Symbol("rr_leaf", INT)
    f = LE(x, Int(10))
    b = BoundedFormula(f)
    r1 = b.refine_domains()
    b2 = BoundedFormula(f)
    r2 = b2.refine_recursive()
    assert r1 is True and r2 is True
    assert b.domains == b2.domains
    assert b.refine_recursive() is False


def test_refine_recursive_and_intersects_children_and_idempotent():
    x = Symbol("rr_and", INT)
    f = And(LE(x, Int(10)), LE(x, Int(3)))
    b = BoundedFormula(f)
    assert b.refine_recursive() is True
    d = b.domains.get(x)
    assert not d.is_top()
    assert d.hull().hi is not None and d.hull().hi <= 3
    assert b.refine_recursive() is False


def test_refine_recursive_and_becomes_bottom_when_ranges_disjoint():
    x = Symbol("rr_bot", INT)
    f = And(LE(x, Int(0)), LE(Int(5), x))
    b = BoundedFormula(f)
    assert b.refine_recursive() is True
    assert b.domains.is_bottom()


def test_refine_domains_context_tightens_leaf_beyond_own_formula():
    x = Symbol("rdx", INT)
    f = LE(x, Int(10))
    b = BoundedFormula(f)
    tighter = LE(x, Int(3))
    assert b.refine_domains(frozenset([tighter])) is True
    hi = b.domains.get(x).hull().hi
    assert hi is not None and hi <= 3


def test_refine_domains_bool_op_root_refines_from_context_only():
    x = Symbol("rbop", INT)
    b = BoundedFormula(And())
    assert b.refine_domains(frozenset([LE(x, Int(7))])) is True
    hi = b.domains.get(x).hull().hi
    assert hi is not None and hi <= 7


def test_refine_recursive_or_does_not_extend_context():
    x = Symbol("ctx_or", INT)
    f = Or(LE(x, Int(1)), LE(x, Int(2)))
    b = BoundedFormula(f)
    assert b.refine_recursive(context=frozenset()) is True


def test_infinte_loop():
    x = Symbol("x", INT)
    f = And(
        Or(
            Equals(x, Int(1)),
            Equals(x, Int(0))
        ),
        Equals(x, Int(1)),
    )

    b = BoundedFormula(f)
    b.refine_recursive()
