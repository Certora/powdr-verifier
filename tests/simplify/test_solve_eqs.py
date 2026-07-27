from src.simplify.solve_eqs import simplify_solve_eqs
from src.smt.utils import *


_AT = ArrayType(INT, INT)


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


def test_scalar_eliminates_const():
    x = Symbol("se_x", INT)
    y = Symbol("se_y", INT)
    smt = _script([
        _decl(x), _decl(y),
        _assert(Equals(x, Int(5))),
        # y has TWO uses so it isn't itself eliminated by the trailing pass.
        _assert(LT(y, Plus(x, Int(1)))),
        _assert(LT(Int(0), y)),
    ])
    out = simplify_solve_eqs(smt)
    assert "se_x" not in _decl_names(out)
    assert "se_y" in _decl_names(out)
    # x has been substituted with 5 in the y assertion.
    asserts = _top_asserts(out)
    assert LT(y, Plus(Int(5), Int(1))) in asserts
    assert LT(Int(0), y) in asserts


def test_scalar_chain():
    x = Symbol("sechain_x", INT)
    y = Symbol("sechain_y", INT)
    z = Symbol("sechain_z", INT)
    smt = _script([
        _decl(x), _decl(y), _decl(z),
        _assert(Equals(y, x)),
        _assert(Equals(x, Int(5))),
        # z has two uses so it survives; we check x and y propagated through.
        _assert(LT(z, Plus(x, y))),
        _assert(LT(Int(0), z)),
    ])
    out = simplify_solve_eqs(smt)
    names = _decl_names(out)
    assert "sechain_x" not in names
    assert "sechain_y" not in names
    assert "sechain_z" in names
    asserts = _top_asserts(out)
    z_assert = next(a for a in asserts if a.node_type() == operators.LT
                    and a.arg(0) == z and a.arg(1) != Int(0))
    rhs = z_assert.arg(1)
    fv = get_env().fvo.get_free_variables(rhs)
    assert x not in fv
    assert y not in fv


def test_array_sym_eq_sym_later_decl_eliminated():
    """When both sides are declared symbols, the later-declared one is
    substituted away (so the earlier name survives)."""
    a = Symbol("sea_early", _AT)
    b = Symbol("sea_late", _AT)
    j = Symbol("sea_j", INT)
    smt = _script([
        _decl(a), _decl(b), _decl(j),
        _assert(Equals(a, b)),
        _assert(Equals(Select(b, j), Int(99))),
        _assert(Equals(Select(a, j), Int(99))),
    ])
    out = simplify_solve_eqs(smt)
    names = _decl_names(out)
    assert "sea_late" not in names, f"expected sea_late dropped, got {names}"
    assert "sea_early" in names
    # Asserts should mention only sea_early (or the constant 99), no sea_late.
    for a_node in _top_asserts(out):
        for sym in get_env().fvo.get_free_variables(a_node):
            assert sym.symbol_name() != "sea_late"


def test_skip_store_rhs():
    """(= arr (store base k v)) is a defining equality and should be
    left for define_inner_array, not substituted by solve_eqs."""
    arr = Symbol("sst_arr", _AT)
    base = Symbol("sst_base", _AT)
    smt = _script([
        _decl(arr), _decl(base),
        _assert(Equals(arr, Store(base, Int(1), Int(2)))),
    ])
    out = simplify_solve_eqs(smt)
    assert "sst_arr" in _decl_names(out)
    # Defining equality kept.
    asserts = _top_asserts(out)
    assert any(a.is_equals() and a.arg(0) == arr for a in asserts)


def test_const_array_rhs_eligible():
    """Const-array `((as const T) v)` is a first-class constant value
    (like scalar 5) — solve_eqs eliminates it."""
    arr = Symbol("sca_arr", _AT)
    j = Symbol("sca_j", INT)
    smt = _script([
        _decl(arr), _decl(j),
        _assert(Equals(arr, Array(INT, Int(7)))),
        _assert(LT(Select(arr, j), Int(100))),
    ])
    out = simplify_solve_eqs(smt)
    assert "sca_arr" not in _decl_names(out)
    # The use of arr has been substituted with the const-array.
    asserts = _top_asserts(out)
    assert LT(Select(Array(INT, Int(7)), j), Int(100)) in asserts


def test_cycle_skipped():
    x = Symbol("scy_x", INT)
    smt = _script([
        _decl(x),
        _assert(Equals(x, Plus(x, Int(1)))),
    ])
    out = simplify_solve_eqs(smt)
    assert "scy_x" in _decl_names(out)
    # The equality survives (cycle, not eligible).
    assert len(_top_asserts(out)) == 1


def test_self_eq_dropped():
    x = Symbol("ssf_x", INT)
    smt = _script([
        _decl(x),
        _assert(Equals(x, x)),
        _assert(Equals(x, Int(7))),
    ])
    out = simplify_solve_eqs(smt)
    # The self-eq is dropped; the (= x 7) eliminates x.
    assert "ssf_x" not in _decl_names(out)
    assert _top_asserts(out) == []


def test_array_eqs_remaining_counter(monkeypatch):
    """The pass reports `array_eqs_remaining` for any (= a b) between
    two array-typed expressions that survives. This is the signal that
    drives the next milestone."""
    captured: dict = {}

    def _capture(_name, data):
        captured.update(data)

    monkeypatch.setattr("src.simplify.solve_eqs.stats_dump", _capture)

    base = Symbol("aer_base", _AT)
    a = Symbol("aer_a", _AT)
    b = Symbol("aer_b", _AT)
    smt = _script([
        _decl(base), _decl(a), _decl(b),
        # Two arrays defined by store -- not eligible for substitution.
        _assert(Equals(a, Store(base, Int(1), Int(2)))),
        _assert(Equals(b, Store(base, Int(2), Int(3)))),
        # Array eq between the two -- eligible.
        _assert(Equals(a, b)),
    ])

    simplify_solve_eqs(smt, None)
    # The eligible (= a b) gets substituted (one of a or b eliminated).
    assert captured["array_eliminations"] >= 1
    # The two store-RHS defining equalities remain; they're array eqs.
    assert captured["array_eqs_remaining"] >= 1


def test_descends_into_conjunction():
    """Eqs inside top-level (and …) are picked up."""
    x = Symbol("sdc_x", INT)
    y = Symbol("sdc_y", INT)
    smt = _script([
        _decl(x), _decl(y),
        _assert(And(Equals(x, Int(5)), LT(y, Int(10)))),
        _assert(LT(Int(0), x)),
    ])
    out = simplify_solve_eqs(smt)
    assert "sdc_x" not in _decl_names(out)
    asserts = _top_asserts(out)
    # The x-eq was eliminated; the conjunction now has only the y-bound.
    # The other assert LT(0, x) becomes LT(0, 5).
    assert LT(Int(0), Int(5)) in asserts
    assert LT(y, Int(10)) in asserts


def test_descends_nested_conjunctions():
    x = Symbol("sdn_x", INT)
    y = Symbol("sdn_y", INT)
    smt = _script([
        _decl(x), _decl(y),
        # Doubly-nested And.
        _assert(And(And(Equals(x, Int(5)), LT(y, Int(10))),
                    LT(Int(0), y))),
    ])
    out = simplify_solve_eqs(smt)
    assert "sdn_x" not in _decl_names(out)


def test_does_not_descend_into_disjunction():
    """(or (= x e) …) is conditional — substitution would be unsound."""
    x = Symbol("sdo_x", INT)
    y = Symbol("sdo_y", INT)
    smt = _script([
        _decl(x), _decl(y),
        _assert(Or(Equals(x, Int(5)), LT(y, Int(0)))),
        _assert(LT(Int(0), x)),
    ])
    out = simplify_solve_eqs(smt)
    # x is still declared; the disjunction is intact.
    assert "sdo_x" in _decl_names(out)


def test_does_not_descend_into_negated_and():
    """(not (and (= x 5) p)) is logically (or (!= x 5) (not p)) —
    elimination of x would be unsound."""
    x = Symbol("sdna_x", INT)
    p = Symbol("sdna_p", BOOL)
    smt = _script([
        _decl(x), _decl(p),
        _assert(Not(And(Equals(x, Int(5)), p))),
        _assert(LT(Int(0), x)),
    ])
    out = simplify_solve_eqs(smt)
    assert "sdna_x" in _decl_names(out)


def test_dispatcher_recognizes_tactic():
    """Smoke test that the tactic name is wired into the dispatcher."""
    from src.simplifier import _apply_tactic_pass, _split_tactic
    smt = _script([])
    # Should not raise; returns the script unchanged.
    out = _apply_tactic_pass(_split_tactic("solve_eqs"), smt, _DummyAction())
    assert out is smt


class _DummyAction:
    def __iadd__(self, other):
        return self
