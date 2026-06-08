from src.simplify.rewrite_store_eqs import simplify_rewrite_store_eqs
from src.smt.utils import *


_AT_1D = ArrayType(INT, INT)
_AT_2D = ArrayType(INT, ArrayType(INT, INT))


def _script(commands):
    s = script.SmtLibScript()
    s.commands = list(commands)
    return s


def _decl(sym):
    return script.SmtLibCommand("declare-fun", [sym])


def _assert(f):
    return script.SmtLibCommand("assert", [f])


def _top_asserts(s):
    return [c.args[0] for c in s.commands if c.name == "assert"]


def test_reflexive_array_eq_drops():
    """(= a a) → True → assert dropped."""
    a = Symbol("rse_a", _AT_1D)
    smt = _script([_decl(a), _assert(Equals(a, a))])
    out = simplify_rewrite_store_eqs(smt)
    assert _top_asserts(out) == []


def test_same_index_same_base_reduces_to_value_eq():
    """(= (store a k v1) (store a k v2)) → (= v1 v2)."""
    a = Symbol("rs_sib_a", _AT_1D)
    v1 = Symbol("rs_sib_v1", INT)
    v2 = Symbol("rs_sib_v2", INT)
    smt = _script([
        _decl(a), _decl(v1), _decl(v2),
        _assert(Equals(Store(a, Int(3), v1), Store(a, Int(3), v2))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    # Same base + same index + same value-type → just (= v1 v2) (And folds away since base_eq is True)
    assert Equals(v1, v2) in asserts


def test_different_constant_indices_reduces():
    """(= (store a 1 v1) (store a 2 v2)) → (and (= v1 a[1]) (= a[2] v2))."""
    a = Symbol("rs_dci_a", _AT_1D)
    v1 = Symbol("rs_dci_v1", INT)
    v2 = Symbol("rs_dci_v2", INT)
    smt = _script([
        _decl(a), _decl(v1), _decl(v2),
        _assert(Equals(Store(a, Int(1), v1), Store(a, Int(2), v2))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    # Should contain (= v1 (select a 1)) AND (= (select a 2) v2)
    asserts = _top_asserts(out)
    combined = And(*asserts) if len(asserts) > 1 else (asserts[0] if asserts else FALSE())
    fv_check = (
        Equals(v1, Select(a, Int(1))),
        Equals(Select(a, Int(2)), v2),
    )
    flat = combined.args() if combined.is_and() else (combined,)
    for fc in fv_check:
        assert fc in flat, f"expected {fc} in {flat}"


def test_store_vs_bare_base_reduces():
    """(= (store a k v) a) → (= v (select a k)). The peeling base_eq (= a a) → True drops."""
    a = Symbol("rs_sbb_a", _AT_1D)
    v = Symbol("rs_sbb_v", INT)
    smt = _script([
        _decl(a), _decl(v),
        _assert(Equals(Store(a, Int(7), v), a)),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    assert Equals(v, Select(a, Int(7))) in asserts


def test_const_array_eq_reduces_to_value_eq():
    """(= ((as const T) v1) ((as const T) v2)) → (= v1 v2)."""
    v1 = Symbol("rs_cae_v1", INT)
    v2 = Symbol("rs_cae_v2", INT)
    smt = _script([
        _decl(v1), _decl(v2),
        _assert(Equals(Array(INT, v1), Array(INT, v2))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    assert Equals(v1, v2) in _top_asserts(out)


def test_2d_nested_store_reduces_to_scalars_when_bases_match():
    """2D store-chains on the SAME base symbol all the way down — the keccak
    shape after solve_store_eqs. The reduction should produce only scalar
    equalities; the base self-equality folds to True at every level."""
    base = Symbol("rs_2d_base", _AT_2D)
    inner = Symbol("rs_2d_inner", _AT_1D)  # SAME inner-array base on both sides
    iv1a = Symbol("rs_2d_iv1a", INT)
    iv1b = Symbol("rs_2d_iv1b", INT)
    iv2a = Symbol("rs_2d_iv2a", INT)
    iv2b = Symbol("rs_2d_iv2b", INT)
    lhs = Store(Store(base, Int(2), Store(inner, Int(4), iv2a)),
                Int(1), Store(inner, Int(8), iv1a))
    rhs = Store(Store(base, Int(2), Store(inner, Int(4), iv2b)),
                Int(1), Store(inner, Int(8), iv1b))
    smt = _script([
        _decl(base), _decl(inner),
        _decl(iv1a), _decl(iv1b), _decl(iv2a), _decl(iv2b),
        _assert(Equals(lhs, rhs)),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    # No residual array-typed Equals at any nesting depth.
    def has_array_eq(node):
        if node.is_equals() and node.arg(0).get_type().is_array_type():
            return True
        return any(has_array_eq(c) for c in node.args())
    for a in asserts:
        assert not has_array_eq(a), f"residual array equality in {a}"


def test_2d_nested_store_leaves_residual_array_eq_when_bases_differ():
    """When the inner-array bases differ between sides, the reducer
    correctly stops at the symbol-vs-symbol level — extensional equality
    on two different symbols is irreducible by purely structural means."""
    base = Symbol("rs_2dd_base", _AT_2D)
    inner_a = Symbol("rs_2dd_ia", _AT_1D)
    inner_b = Symbol("rs_2dd_ib", _AT_1D)
    iv1 = Symbol("rs_2dd_iv1", INT)
    iv2 = Symbol("rs_2dd_iv2", INT)
    lhs = Store(base, Int(1), Store(inner_a, Int(8), iv1))
    rhs = Store(base, Int(1), Store(inner_b, Int(8), iv2))
    smt = _script([
        _decl(base), _decl(inner_a), _decl(inner_b), _decl(iv1), _decl(iv2),
        _assert(Equals(lhs, rhs)),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    # The reducer produces (and (= iv1 iv2) (= inner_a inner_b)) — the
    # second is the irreducible residue.
    found_residual = False
    def walk(node):
        nonlocal found_residual
        if node.is_equals() and node.arg(0).get_type().is_array_type():
            if node.arg(0) == inner_a and node.arg(1) == inner_b:
                found_residual = True
        for c in node.args():
            walk(c)
    for a in asserts:
        walk(a)
    assert found_residual


def test_variable_index_left_alone():
    """Variable-index stores can't be statically reduced when sides have
    different/missing matching index — leave alone."""
    a = Symbol("rs_vi_a", _AT_1D)
    v = Symbol("rs_vi_v", INT)
    i = Symbol("rs_vi_i", INT)
    smt = _script([
        _decl(a), _decl(v), _decl(i),
        _assert(Equals(Store(a, i, v), a)),
    ])
    out = simplify_rewrite_store_eqs(smt)
    # Equality preserved unchanged (or as Equals on stored expression).
    asserts = _top_asserts(out)
    assert any(x.is_equals() for x in asserts)


def test_same_variable_index_reduces_to_value_eq():
    """`(= (store a k v1) (store a k v2))` reduces to `(= v1 v2)` even when
    `k` is a variable expression — only the SAME index FNode on both sides
    is required."""
    a = Symbol("rs_svi_a", _AT_1D)
    x = Symbol("rs_svi_x", INT)
    y = Symbol("rs_svi_y", INT)
    v1 = Symbol("rs_svi_v1", INT)
    v2 = Symbol("rs_svi_v2", INT)
    # Same arithmetic expression for the index on both sides — hash-consed
    # to the same FNode by pysmt.
    idx_expr = Plus(x, y)
    smt = _script([
        _decl(a), _decl(x), _decl(y), _decl(v1), _decl(v2),
        _assert(Equals(Store(a, idx_expr, v1), Store(a, idx_expr, v2))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    # Should reduce to just (= v1 v2) (base self-eq folds).
    assert Equals(v1, v2) in asserts


def test_canonicalizer_handles_mod_distributive_and_operand_order():
    """The keccak post-flatten case: indices differ syntactically by
    Times-operand order AND inner-Mod wrappers under outer Mod(_, p).
    Canonicalization should make them compare equal so the reducer fires."""
    a = Symbol("rs_cn_a", _AT_1D)
    x = Symbol("rs_cn_x", INT)
    y = Symbol("rs_cn_y", INT)
    v1 = Symbol("rs_cn_v1", INT)
    v2 = Symbol("rs_cn_v2", INT)
    p = Int(2013265921)
    # Index forms:
    # LHS: (((x * 65536) + y) % p)
    idx_lhs = Plus(Times(x, Int(65536)), y) % p if False else \
        get_env().formula_manager.Mod(
            Plus(Times(x, Int(65536)), y), p)
    # RHS: (((65536 * (x % p)) + (y % p)) % p)
    mgr = get_env().formula_manager
    idx_rhs = mgr.Mod(
        Plus(Times(Int(65536), mgr.Mod(x, p)), mgr.Mod(y, p)),
        p,
    )
    smt = _script([
        _decl(a), _decl(x), _decl(y), _decl(v1), _decl(v2),
        _assert(Equals(Store(a, idx_lhs, v1), Store(a, idx_rhs, v2))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    # After canonicalization, the two store indices match, so the eq
    # reduces to (= v1 v2).
    assert Equals(v1, v2) in asserts


def test_same_variable_index_inside_negated_disjunct_reduces():
    """The keccak shape: `(or … (not (and … (= (store a k v1) (store a k v2)) …)) …)`
    The inner array equality reduces to `(= v1 v2)`, which IS reducible to
    a scalar — collapsing the conditional cleanly even though k is variable."""
    a = Symbol("rs_svid_a", _AT_1D)
    x = Symbol("rs_svid_x", INT)
    v1 = Symbol("rs_svid_v1", INT)
    v2 = Symbol("rs_svid_v2", INT)
    p = Symbol("rs_svid_p", BOOL)
    idx = Times(Int(65536), x)
    inner_eq = Equals(Store(a, idx, v1), Store(a, idx, v2))
    smt = _script([
        _decl(a), _decl(x), _decl(v1), _decl(v2), _decl(p),
        _assert(Or(p, Not(And(inner_eq, p)))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)

    def contains_array_eq(node):
        if node.is_equals() and node.arg(0).get_type().is_array_type():
            return True
        return any(contains_array_eq(c) for c in node.args())

    for n in asserts:
        assert not contains_array_eq(n), f"residual array eq in {n}"


def test_not_of_store_eq_propagates_after_reduction():
    """(not (= (store a k v) (store a k v'))) — after reduction the inner
    becomes (= v v'); the (not …) stays around it."""
    a = Symbol("rs_n_a", _AT_1D)
    v = Symbol("rs_n_v", INT)
    v2 = Symbol("rs_n_v2", INT)
    smt = _script([
        _decl(a), _decl(v), _decl(v2),
        _assert(Not(Equals(Store(a, Int(1), v), Store(a, Int(1), v2)))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    asserts = _top_asserts(out)
    assert Not(Equals(v, v2)) in asserts


def test_or_with_reduced_false_disjunct_drops_disjunct():
    """(or p (= a a)) — the array reflexivity reduces to True, OR becomes True, assert drops."""
    a = Symbol("rs_or_a", _AT_1D)
    p = Symbol("rs_or_p", BOOL)
    smt = _script([
        _decl(a), _decl(p),
        _assert(Or(p, Equals(a, a))),
    ])
    out = simplify_rewrite_store_eqs(smt)
    # Or((= a a), p) → Or(True, p) → True → assert drops.
    assert _top_asserts(out) == []


def test_dispatcher_recognizes_tactic():
    from src.simplifier import _apply_tactic_pass

    class _DummyAction:
        def __iadd__(self, other):
            return self

    smt = _script([])
    out = _apply_tactic_pass("rewrite_store_eqs", [], smt, _DummyAction())
    assert out is smt
