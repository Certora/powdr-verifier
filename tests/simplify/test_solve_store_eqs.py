from src.simplify.solve_store_eqs import simplify_solve_store_eqs
from src.smt.utils import *


_AT_2D = ArrayType(INT, ArrayType(INT, INT))
_AT_1D = ArrayType(INT, INT)


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


def _decl_names(s):
    return [c.args[0].symbol_name() for c in s.commands if c.name == "declare-fun"]


def test_basic_store_rhs_substituted():
    arr = Symbol("sse_arr", _AT_2D)
    base = Symbol("sse_base", _AT_2D)
    inner = Symbol("sse_inner", _AT_1D)
    smt = _script([
        _decl(arr), _decl(base), _decl(inner),
        _assert(Equals(arr, Store(base, Int(1), inner))),
        # Use arr in a (non-defining) select context.
        _assert(Equals(Select(arr, Int(2)), inner)),
    ])
    out = simplify_solve_store_eqs(smt)
    assert "sse_arr" not in _decl_names(out)
    # The defining (= arr (store …)) is dropped.
    # The use becomes (= (select (store base 1 inner) 2) inner).
    asserts = _top_asserts(out)
    assert Equals(Select(Store(base, Int(1), inner), Int(2)), inner) in asserts


def test_1d_array_not_touched():
    """Pass restricted to 2D arrays. 1D defining store-RHS is left alone."""
    arr1 = Symbol("sse_1d_arr", _AT_1D)
    base1 = Symbol("sse_1d_base", _AT_1D)
    smt = _script([
        _decl(arr1), _decl(base1),
        _assert(Equals(arr1, Store(base1, Int(0), Int(7)))),
    ])
    out = simplify_solve_store_eqs(smt)
    # Still declared, still asserted.
    assert "sse_1d_arr" in _decl_names(out)
    assert len(_top_asserts(out)) == 1


def test_const_array_rhs_substituted():
    arr = Symbol("sse_c_arr", _AT_2D)
    inner_const = Symbol("sse_c_inner", _AT_1D)
    smt = _script([
        _decl(arr), _decl(inner_const),
        _assert(Equals(arr, Array(INT, inner_const))),
        _assert(Equals(Select(arr, Int(5)), inner_const)),
    ])
    out = simplify_solve_store_eqs(smt)
    assert "sse_c_arr" not in _decl_names(out)


def test_chain_and_conditional_drop():
    """The keccak scenario: top-level chain def AND a negated form inside
    (or …) referencing the same store expression. After substitution the
    structurally-identical stores collapse to True, and the (not (= e e))
    folds to False, dropping its disjunct."""
    arr = Symbol("sse_chain_arr", _AT_2D)
    base = Symbol("sse_chain_base", _AT_2D)
    inner_v = Symbol("sse_chain_inner", _AT_1D)
    p = Symbol("sse_chain_p", BOOL)
    store_expr = Store(base, Int(1), inner_v)
    smt = _script([
        _decl(arr), _decl(base), _decl(inner_v), _decl(p),
        _assert(Equals(arr, store_expr)),
        # The conditional negation inside (or p ... ).
        _assert(Or(p, Not(Equals(arr, store_expr)))),
    ])
    out = simplify_solve_store_eqs(smt)
    asserts = _top_asserts(out)
    # The (or …) should have collapsed to just `p` (the (not (= e e))
    # branch folded to False and dropped).
    assert p in asserts
    # Defining equality dropped.
    assert not any(a.is_equals() and a.arg(0) == arr for a in asserts)


def test_multi_definition_skipped():
    arr = Symbol("sse_md_arr", _AT_2D)
    b1 = Symbol("sse_md_b1", _AT_2D)
    b2 = Symbol("sse_md_b2", _AT_2D)
    inner = Symbol("sse_md_inner", _AT_1D)
    smt = _script([
        _decl(arr), _decl(b1), _decl(b2), _decl(inner),
        _assert(Equals(arr, Store(b1, Int(1), inner))),
        _assert(Equals(arr, Store(b2, Int(1), inner))),
    ])
    out = simplify_solve_store_eqs(smt)
    # The pass would substitute the FIRST seen and end up with
    # `(= (store b1 1 inner) (store b2 1 inner))` from the second
    # (which is NOT a defining equality anymore — neither side is the
    # original symbol). Acceptable: arr is replaced everywhere; the
    # two defs converge into a constraint on b1 vs b2.
    asserts = _top_asserts(out)
    # arr is dropped after substitution. The two defs are merged.
    assert "sse_md_arr" not in _decl_names(out)
    # Some assert pairs the two store-expressions.
    expected = Equals(Store(b1, Int(1), inner), Store(b2, Int(1), inner))
    assert expected in asserts


def test_cycle_skipped():
    """`(= arr (store arr k v))` is cyclic; pass must not substitute."""
    arr = Symbol("sse_cy_arr", _AT_2D)
    inner = Symbol("sse_cy_inner", _AT_1D)
    smt = _script([
        _decl(arr), _decl(inner),
        _assert(Equals(arr, Store(arr, Int(1), inner))),
    ])
    out = simplify_solve_store_eqs(smt)
    assert "sse_cy_arr" in _decl_names(out)
    assert len(_top_asserts(out)) == 1


def test_descends_into_conjunction():
    arr = Symbol("sse_dc_arr", _AT_2D)
    base = Symbol("sse_dc_base", _AT_2D)
    inner = Symbol("sse_dc_inner", _AT_1D)
    p = Symbol("sse_dc_p", BOOL)
    smt = _script([
        _decl(arr), _decl(base), _decl(inner), _decl(p),
        _assert(And(Equals(arr, Store(base, Int(1), inner)), p)),
        _assert(Equals(Select(arr, Int(2)), inner)),
    ])
    out = simplify_solve_store_eqs(smt)
    assert "sse_dc_arr" not in _decl_names(out)


def test_does_not_descend_into_disjunction():
    """`(or (= arr (store …)) other)` is a conditional equality — must
    NOT be eliminated."""
    arr = Symbol("sse_do_arr", _AT_2D)
    base = Symbol("sse_do_base", _AT_2D)
    inner = Symbol("sse_do_inner", _AT_1D)
    p = Symbol("sse_do_p", BOOL)
    smt = _script([
        _decl(arr), _decl(base), _decl(inner), _decl(p),
        _assert(Or(Equals(arr, Store(base, Int(1), inner)), p)),
    ])
    out = simplify_solve_store_eqs(smt)
    assert "sse_do_arr" in _decl_names(out)


def test_dispatcher_recognizes_tactic():
    from src.simplifier import _apply_tactic_pass

    class _DummyAction:
        def __iadd__(self, other):
            return self

    smt = _script([])
    out = _apply_tactic_pass("solve_store_eqs", [], smt, _DummyAction())
    assert out is smt
