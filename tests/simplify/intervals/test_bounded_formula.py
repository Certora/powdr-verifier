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
