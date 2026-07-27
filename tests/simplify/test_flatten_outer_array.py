"""Tests for ``simplify_flatten_outer_array``."""
import pytest
from pysmt.typing import ArrayType

from src.simplify.flatten_outer_array import simplify_flatten_outer_array
from src.smt.utils import *


OuterTy = ArrayType(INT, ArrayType(INT, INT))
InnerTy = ArrayType(INT, INT)


def _script(decls, *asserts):
    s = script.SmtLibScript()
    s.commands = []
    for sym in decls:
        s.commands.append(script.SmtLibCommand(
            "declare-fun", [sym, [], sym.get_type()]))
    for f in asserts:
        s.commands.append(script.SmtLibCommand("assert", [f]))
    s.commands.append(script.SmtLibCommand("check-sat", []))
    return s


def _decl_names_of(s):
    return [c.args[0].symbol_name() for c in s if c.name == "declare-fun"]


def _asserts_of(s):
    return [c.args[0] for c in s if c.name == "assert"]


def test_flatten_splits_outer_decl_into_per_k_inner_decls():
    """An outer-array with constant outer accesses gets split into inner decls."""
    M = Symbol("M", OuterTy)
    inner = Symbol("inner", InnerTy)
    addr = Symbol("addr", INT)

    s = _script(
        [M, inner, addr],
        # (= inner (select M 1))
        Equals(inner, Select(M, Int(1))),
        # (= M (store M 2 inner))   -- forces outer index 2 to be observed
        Equals(M, Store(M, Int(2), inner)),
    )

    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)

    assert "M" not in names, "outer decl should be dropped"
    assert "M__1" in names, "inner decl for index 1 should be present"
    assert "M__2" in names, "inner decl for index 2 should be present"


def test_flatten_select_at_constant_resolves_recursively():
    """``(select M 1)`` rewrites; the pass runs to a fixpoint so inner-array
    decls created by the first round may themselves be flattened further if
    their elements get observed at constant indices.
    """
    M = Symbol("M2", OuterTy)
    inner = Symbol("inner2", InnerTy)
    s = _script(
        [M, inner],
        Equals(inner, Select(M, Int(1))),
        # observe index 2 too so M is flatten-eligible with K = {1, 2}
        Equals(inner, Select(M, Int(2))),
    )
    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)
    # M is gone; either M__1/M__2 or their further-flattened scalars survive.
    assert "M2" not in names
    # Some symbol containing "M2__" must be present (per-k decl, possibly
    # recursively split further).
    assert any(n.startswith("M2__") for n in names)
    # No outer-typed (2-level) array names should remain.
    for cmd in out.commands:
        if cmd.name != "declare-fun":
            continue
        ty = cmd.args[0].get_type()
        assert not (ty.is_array_type() and ty.elem_type.is_array_type()), (
            f"residual outer-typed decl: {cmd.args[0].symbol_name()}: {ty}"
        )


def test_flatten_store_equality_expands_to_paired_inner_equalities():
    """``(= NEW (store OLD k V))`` becomes two inner equalities."""
    OLD = Symbol("OLD", OuterTy)
    NEW = Symbol("NEW", OuterTy)
    V = Symbol("V", InnerTy)
    s = _script(
        [OLD, NEW, V],
        Equals(NEW, Store(OLD, Int(1), V)),
        # observe outer index 2 on OLD so both inner arrays get declared
        Equals(NEW, Store(OLD, Int(2), V)),
    )
    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)
    assert {"OLD__1", "OLD__2", "NEW__1", "NEW__2"}.issubset(names)
    assert "OLD" not in names and "NEW" not in names
    # Every emitted assertion should be inner-typed (no Outer-typed eq remains)
    for f in _asserts_of(out):
        for arg in f.args() if not f.is_equals() else [f.arg(0), f.arg(1)]:
            t = arg.get_type()
            assert not (t.is_array_type() and t.elem_type.is_array_type()), \
                f"residual outer-typed expression: {arg}"


def test_flatten_hard_fails_when_variable_index_outer_access():
    """A single variable-index outer access disqualifies the array; flatten
    now hard-fails because the array can't be eliminated. Per the new
    contract: no 2D+ array may survive the pass."""
    M = Symbol("M3", OuterTy)
    inner = Symbol("inner3", InnerTy)
    addr = Symbol("addr3", INT)
    i = Symbol("i", INT)
    s = _script(
        [M, inner, addr, i],
        Equals(inner, Select(M, Int(1))),  # constant — fine
        Equals(inner, Select(M, i)),       # variable outer index — disqualifies M
    )
    with pytest.raises(AssertionError, match="2D\\+ array.*still referenced"):
        simplify_flatten_outer_array(s)


def test_flatten_hard_fails_when_outer_used_outside_array_positions():
    """An outer array used in a non-array position disqualifies it; flatten
    hard-fails because the array can't be eliminated. Per the new contract:
    no 2D+ array may survive the pass."""
    # Use Ite to "consume" the outer-typed value in a non-select/store/eq slot.
    M = Symbol("M4", OuterTy)
    N = Symbol("N4", OuterTy)
    cond = Symbol("cond_flag", BOOL)  # not "c": pysmt's global symbol cache clashes
    # with an INT "c" defined by another test collected earlier in the same run
    inner = Symbol("inner4", InnerTy)
    expr = Ite(cond, M, N)  # outer-typed result, in an Ite (parent is array-typed)
    s = _script(
        [M, N, cond, inner],
        Equals(inner, Select(expr, Int(1))),
    )
    with pytest.raises(AssertionError, match="2D\\+ array.*still referenced"):
        simplify_flatten_outer_array(s)


def test_flatten_outer_array_equality_expands():
    """``(= A B)`` on outer arrays expands per-k. With fixpoint flattening,
    the inner ``A__k`` / ``B__k`` arrays may themselves be split further,
    so the eventual ground form pairs scalar leaves of ``A`` and ``B``
    (e.g., ``A__1__1 = B__1__1``).
    """
    A = Symbol("A", OuterTy)
    B = Symbol("B", OuterTy)
    inner = Symbol("innerAB", InnerTy)
    s = _script(
        [A, B, inner],
        Equals(A, B),
        Equals(inner, Select(A, Int(1))),
        Equals(inner, Select(B, Int(2))),
    )
    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)
    # A, B themselves should be gone (replaced by per-k leaves).
    assert "A" not in names and "B" not in names
    # No outer-typed decls should survive.
    for cmd in out.commands:
        if cmd.name != "declare-fun":
            continue
        ty = cmd.args[0].get_type()
        assert not (ty.is_array_type() and ty.elem_type.is_array_type()), (
            f"residual outer-typed decl: {cmd.args[0].symbol_name()}: {ty}"
        )
    # Some pair of A-leaf / B-leaf scalars (or arrays) should appear in an
    # equality somewhere — verifying the (= A B) constraint propagated to
    # the leaves of both.
    paired = False
    for f in _asserts_of(out):
        stack = [f]
        while stack:
            node = stack.pop()
            if node.is_and() or node.is_or() or node.is_not():
                stack.extend(node.args())
                continue
            if node.is_equals():
                lhs, r = node.arg(0), node.arg(1)
                if lhs.is_symbol() and r.is_symbol():
                    ln, rn = lhs.symbol_name(), r.symbol_name()
                    if ln.startswith("A") and rn.startswith("B") or \
                       ln.startswith("B") and rn.startswith("A"):
                        paired = True
    assert paired, "expected at least one A-leaf == B-leaf equality"


def test_flatten_idempotent_on_already_flat_formula():
    """Running the pass on a formula with no outer arrays is a no-op."""
    a = Symbol("a", INT)
    s = _script([a], LE(a, Int(0)))
    cmds_before = list(s.commands)
    out = simplify_flatten_outer_array(s)
    assert [c.name for c in out.commands] == [c.name for c in cmds_before]


def test_flatten_extensional_equality_preserved_on_observed_indices():
    """The pass's per-k expansion of ``(= A B)`` is sat-equivalent on the
    observed-index set: a counterexample at an unobserved index is impossible
    because nothing in the formula constrains those indices."""
    # This test verifies the soundness invariant by construction: we set up a
    # formula where A and B differ only at index 99 (no constraint at 99) and
    # check that the rewritten formula remains sat (extension still exists).
    # If the pass were unsoundly forcing A == B everywhere, this would go
    # unsat after the rewrite. (We don't invoke z3 here; we just check that
    # the rewrite doesn't insert any cross-index equality.)
    A = Symbol("Aex", OuterTy)
    B = Symbol("Bex", OuterTy)
    inner = Symbol("innerex", InnerTy)
    s = _script(
        [A, B, inner],
        Equals(inner, Select(A, Int(1))),
        Equals(inner, Select(B, Int(1))),
        Not(Equals(A, B)),  # outer-typed inequality
    )
    out = simplify_flatten_outer_array(s)
    # After flatten: K = {1}. (not (= A B)) becomes (not (= A__1 B__1)).
    # There is NO assertion mentioning Aex__2 or Bex__2 (no observed K=2).
    full_text = "\n".join(str(c.args[0]) for c in out if c.name == "assert")
    assert "Aex__2" not in full_text
    assert "Bex__2" not in full_text
    assert "Aex__1" in full_text and "Bex__1" in full_text
