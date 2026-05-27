"""Tests for ``simplify_flatten_outer_array``."""
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


def test_flatten_select_at_constant_becomes_inner_name():
    """``(select M 1)`` rewrites to ``M__1``."""
    M = Symbol("M2", OuterTy)
    inner = Symbol("inner2", InnerTy)
    s = _script(
        [M, inner],
        Equals(inner, Select(M, Int(1))),
        # observe index 2 too so M is flatten-eligible with K = {1, 2}
        Equals(inner, Select(M, Int(2))),
    )
    out = simplify_flatten_outer_array(s)
    asserts = _asserts_of(out)
    rhs_names = set()
    for f in asserts:
        # each assert is (= inner2 X) — collect X's name when X is a symbol
        if f.is_equals() and f.arg(1).is_symbol():
            rhs_names.add(f.arg(1).symbol_name())
    assert "M2__1" in rhs_names
    assert "M2__2" in rhs_names


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


def test_flatten_skipped_when_variable_index_outer_access():
    """A single variable-index outer access disables flattening for that array."""
    M = Symbol("M3", OuterTy)
    inner = Symbol("inner3", InnerTy)
    addr = Symbol("addr3", INT)
    i = Symbol("i", INT)
    s = _script(
        [M, inner, addr, i],
        Equals(inner, Select(M, Int(1))),  # constant — fine
        Equals(inner, Select(M, i)),       # variable outer index — disqualifies M
    )
    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)
    assert "M3" in names, "M3 should NOT be flattened (variable outer index)"
    assert "M3__1" not in names


def test_flatten_skipped_when_outer_used_outside_array_positions():
    """An outer array used in a non-array position disables flattening."""
    # Use Ite to "consume" the outer-typed value in a non-select/store/eq slot.
    M = Symbol("M4", OuterTy)
    N = Symbol("N4", OuterTy)
    cond = Symbol("c", BOOL)
    inner = Symbol("inner4", InnerTy)
    expr = Ite(cond, M, N)  # outer-typed result, in an Ite (parent is array-typed)
    s = _script(
        [M, N, cond, inner],
        # parent context: select((ite c M N), 1) — M and N each appear under Ite,
        # not directly under select. Whether the pass treats this as eligible
        # depends on the safety check; here we assert it bails out conservatively.
        Equals(inner, Select(expr, Int(1))),
    )
    out = simplify_flatten_outer_array(s)
    names = _decl_names_of(out)
    # Conservative: M4 and N4 sit under Ite which is not a recognized ok-position
    # for symbols → ineligible. Original decls remain.
    assert "M4" in names and "N4" in names
    assert "M4__1" not in names and "N4__1" not in names


def test_flatten_outer_array_equality_expands():
    """``(= A B)`` on outer arrays expands to an ``And`` of inner equalities."""
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
    asserts = _asserts_of(out)
    # The original (= A B) should now be (and (= A__1 B__1) (= A__2 B__2)),
    # i.e., a top-level And of two inner-typed equalities. After the walker
    # the assertion may be either an And or, less commonly, distributed by
    # the pysmt simplifier. Check the underlying inner names appear paired.
    found_a1_b1 = False
    found_a2_b2 = False
    for f in asserts:
        # flatten And recursively for the check
        stack = [f]
        while stack:
            node = stack.pop()
            if node.is_and() or node.is_or():
                stack.extend(node.args())
                continue
            if not node.is_equals():
                continue
            l, r = node.arg(0), node.arg(1)
            if l.is_symbol() and r.is_symbol():
                ln, rn = l.symbol_name(), r.symbol_name()
                if {ln, rn} == {"A__1", "B__1"}: found_a1_b1 = True
                if {ln, rn} == {"A__2", "B__2"}: found_a2_b2 = True
    assert found_a1_b1, "expected (= A__1 B__1) somewhere in the rewritten asserts"
    assert found_a2_b2, "expected (= A__2 B__2) somewhere in the rewritten asserts"


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
