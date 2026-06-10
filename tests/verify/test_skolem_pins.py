from src.verify import SetInfos, SkolemPin, SkolemPinKind
from src.verify.skolem_pins import drop_mirrored_derived
from src.smt.utils import *


def _sym(name: str) -> FNode:
    return Symbol(name, INT)


def _quotient_or_zero(var: FNode, num: FNode, den: FNode) -> FNode:
    uf_mod_inv = Symbol("uf_mod_inv", FunctionType(INT, [INT]))
    return Equals(
        var,
        Ite(Equals(den, Int(0)), Int(0), Times(num, Function(uf_mod_inv, [den]))),
    )


def test_mirrored_derived_columns_are_dropped():
    b_v, a_v = _sym("before-inv_of_sum_1"), _sym("after-inv_of_sum_1")
    b_x, a_x = _sym("before-x"), _sym("after-x")
    before = {b_v: _quotient_or_zero(b_v, Int(1), b_x)}
    after = {a_v: _quotient_or_zero(a_v, Int(1), a_x)}

    assert drop_mirrored_derived(after, before, "after-", "before-") == {}
    assert drop_mirrored_derived(before, after, "before-", "after-") == {}


def test_diverging_derived_columns_are_kept():
    b_v, a_v = _sym("before-inv_of_sum_1"), _sym("after-inv_of_sum_1")
    b_x, a_x = _sym("before-x"), _sym("after-x")
    # same column name, but different defining expressions (numerator differs)
    before = {b_v: _quotient_or_zero(b_v, Int(1), b_x)}
    after = {a_v: _quotient_or_zero(a_v, Int(2), a_x)}

    assert drop_mirrored_derived(after, before, "after-", "before-") == after
    assert drop_mirrored_derived(before, after, "before-", "after-") == before


def test_derived_column_without_counterpart_is_kept():
    a_v = _sym("after-inv_of_sum_1")
    a_x = _sym("after-x")
    after = {a_v: _quotient_or_zero(a_v, Int(1), a_x)}

    assert drop_mirrored_derived(after, {}, "after-", "before-") == after


def test_set_infos_preserves_per_pin_types():
    a = SetInfos(equations=[SkolemPin(Int(0), SkolemPinKind.DERIVED)])
    a += SetInfos(equations=[SkolemPin(Int(1), SkolemPinKind.SUBSTITUTION)])
    assert [p.pin_type for p in a.equations] == [
        SkolemPinKind.DERIVED,
        SkolemPinKind.SUBSTITUTION,
    ]


def test_mixed_derived_columns_filter_only_mirrored():
    b_v, a_v = _sym("before-inv_of_sum_1"), _sym("after-inv_of_sum_1")
    b_w, a_w = _sym("before-free_var_2"), _sym("after-free_var_2")
    b_x, a_x = _sym("before-x"), _sym("after-x")
    before = {
        b_v: _quotient_or_zero(b_v, Int(1), b_x),
        b_w: Equals(b_w, Int(0)),
    }
    after = {
        a_v: _quotient_or_zero(a_v, Int(1), a_x),
        a_w: Equals(a_w, Int(7)),  # constant differs -> not mirrored
    }

    assert drop_mirrored_derived(after, before, "after-", "before-") == {a_w: after[a_w]}
