"""Constant propagation for memory-bus multiplicities."""
import json
from pathlib import Path

import pytest

from src.lens.normalize import BABYBEAR_PRIME as P
from src.membus import keys, propagate
from src.membus.busmodel import symbolic_as_ordinals
from src.membus.linform import LinForm, linform
from src.membus.rules import Analysis

_DUMP = (Path(__file__).resolve().parents[2]
         / "powdr-dumps/guest-keccak-selection"
         / "apc_candidate_2103992_002_loop_iteration.json")
_DUMP_2100223 = (Path(__file__).resolve().parents[2]
                 / "powdr-dumps/guest-keccak-selection"
                 / "apc_candidate_2100223_000_unopt.json")
_DUMP_2103992 = (Path(__file__).resolve().parents[2]
                 / "powdr-dumps/guest-keccak-selection"
                 / "apc_candidate_2103992_000_unopt.json")
_DUMP_2103993 = (Path(__file__).resolve().parents[2]
                 / "powdr-dumps/guest-keccak-selection"
                 / "apc_candidate_2103993_000_unopt.json")
_DUMP_2099828 = (Path(__file__).resolve().parents[2]
                 / "powdr-dumps/guest-keccak"
                 / "apc_candidate_2099828_001_exec_bus.json")


def _an(cons=(), bis=()):
    return Analysis({"constraints": list(cons), "bus_interactions": list(bis)})


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


def _bool(col: str):
    return [col, "*", [col, "+", -1]]


def _ternary_bool(col: str):
    return [col, "*", [[col, "-", 1], "*", [col, "-", 2]]]


def test_linform_subst_folds_pins():
    lf = LinForm.make({"a@1": 1, "b@2": -1}, 3)
    assert lf.subst({"a@1": 5, "b@2": 2}) == LinForm.make({}, 6)


def test_same_coeff_offset():
    flags = ("f0@1", "f1@2")
    cons = [_bool(flags[0]), _bool(flags[1]),
            _add(_m(-1, flags[0]), _m(-1, flags[1]), 1)]
    mult = ["-", _add(flags[0], flags[1])]
    an = _an(cons, [{"id": 1, "mult": mult, "args": [1, 8, 0, 0, 0, 0, "t@3"]}])
    assert an.kinds[0].kind == "recv"


def test_negated_coeff_offset():
    flags = ("f0@1", "f1@2")
    cons = [_bool(flags[0]), _bool(flags[1]),
            _add(_m(-1, flags[0]), _m(-1, flags[1]), 1)]
    mult = _add(flags[0], flags[1])
    an = _an(cons, [{"id": 1, "mult": mult, "args": [1, 8, 0, 0, 0, 0, "t@3"]}])
    assert an.kinds[0].kind == "send"


def test_single_column_pin():
    cons = [_bool("g@1"), _add("g@1", -1)]
    an = Analysis({"constraints": cons,
                   "bus_interactions": [{"id": 1, "mult": "g@1",
                                         "args": [1, 8, 0, 0, 0, 0, "t@2"]}]},
                  assume_is_valid=False)
    assert an.kinds[0].kind == "send"
    assert an._propagation.pins["g@1"].value == 1
    assert an.kinds[0].premises


def test_chained_substitution():
    cons = [_bool("a@2"), _bool("b@1"),
            _add("b@1", -1), _add("a@2", "b@1", -1)]
    an = Analysis({"constraints": cons,
                   "bus_interactions": [{"id": 1, "mult": ["-", "a@2"],
                                         "args": [1, 8, 0, 0, 0, 0, "t@3"]}]},
                  assume_is_valid=False)
    assert an.kinds[0].kind == "disabled"


def test_boolean_gadget_enables_pin_window():
    cons = [["c@1", "*", ["c@1", "+", -1]], _add("c@1", -1)]
    an = _an(cons, [{"id": 1, "mult": "c@1", "args": [1, 8, 0, 0, 0, 0, "t@2"]}])
    assert an.kinds[0].kind == "send"


@pytest.mark.skipif(not _DUMP.is_file(), reason="regression dump not present")
def test_loop_iteration_dump_all_kinds_resolved():
    data = json.loads(_DUMP.read_text())
    an = Analysis(data, assume_is_valid=False)
    for row in an.mem:
        k = an.kinds.get(row.ordinal)
        assert k is not None, f"ordinal {row.ordinal} mult {row.mult!r}"


def test_eval_mult_direct():
    mf = linform(["-", "x@1"])
    prop = propagate.propagate(_an([_bool("x@1"), _add("x@1", -1)]))
    assert prop.pins["x@1"].value == 1
    assert propagate.eval_mult(mf, prop) == P - 1


def test_eval_expr_resolves_as_and_pointer():
    cons = [_add("as@1", -2), _add("ptr@3", -8)]
    bis = [{"id": 1, "mult": 1, "args": ["as@1", "ptr@3", 0, 0, 0, 0, "t@4"]}]
    an = _an(cons, bis)
    row = an.mem[0]
    assert row.addr_space_expr == 2
    assert row.ptr == 8
    assert keys.recover_key(an, row) == keys.Const(8)


def test_ternary_boolean_gadget_bounds():
    cons = [_ternary_bool("f@1"), _add("f@1", -1)]
    an = _an(cons, [{"id": 1, "mult": "f@1", "args": [1, 8, 0, 0, 0, 0, "t@2"]}])
    assert an.kinds[0].kind == "send"


def test_single_col_constraint_bounds_exact_residue():
    """A single-column constraint pins the column's EXACT residue, even one
    >= 2^29. The old Bound(col, 0, 2^29) was false for large residues; trusted
    as a window premise a false bound can certify a false integer identity."""
    an = _an(cons=[["col@1", "+", 1]])          # col + 1 = 0  ->  col = P - 1
    b = propagate.prop_bound_facts(an)["col@1"]
    assert (b.lo, b.hi) == (P - 1, P)           # exact, not [0, 2^29)


def test_large_residue_column_yields_no_integer_zero():
    """With the exact residue bound, a term touching a large-residue column has
    an out-of-window integer span, so no (unsound) integer LinZero is emitted.
    Under the old loose bound `y - 2*col = 0` certified though `col = P-1`
    makes it false by exactly P."""
    an = _an(cons=[["col@1", "+", 1], ["y@2", "-", _m(2, "col@1")]])
    zero_cols = {z.coeffs for z in propagate.propagate(an).zeros}
    assert (("col@1", -2), ("y@2", 1)) not in zero_cols
    assert (("y@2", 1), ("col@1", -2)) not in zero_cols


def test_product_gadget_bounds_only_boolean_form():
    """(col+a)(col+a-1)=0 has roots {-a, 1-a}; [0,2) is sound only for a=0."""
    boolean = propagate.prop_bound_facts(_an(cons=[_bool("x@1")]))["x@1"]
    assert (boolean.lo, boolean.hi) == (0, 2)
    shifted = [["x@1", "+", 5], "*", ["x@1", "+", 4]]     # (x+5)(x+4)=0
    assert propagate.prop_bound_facts(_an(cons=[shifted])).get("x@1") is None


def test_decoding_index_flipped_mux_form():
    is_load = "is_load_0@10"
    poly = ["flags__0_0@5", "*", 2]
    cons = [_add(poly, is_load)]
    index = propagate._DecodingIndex.build(cons)
    assert is_load in index.mux_by_is_load
    assert index.mux_by_is_load[is_load][1] == cons[0]


def test_fold_pins_algebraic_identities():
    col = "mem_ptr_limbs__0_1@52"
    assert propagate._fold_pins([0, "+", [1, "*", col]], {}) == col
    assert propagate._fold_pins([col, "+", 0], {}) == col
    assert propagate._fold_pins([col, "-", 0], {}) == col
    assert propagate._fold_pins([[1, "*", col], "*", 1], {}) == col
    assert propagate._fold_pins([0, "-", col], {}) == ["-", col]


def test_fold_pins_relative_toward_base():
    rel = {"ts_b@2": ("ts_a@1", 3)}
    assert propagate._fold_pins("ts_b@2", {}, rel) == ["ts_a@1", "+", 3]
    assert propagate._fold_pins("ts_a@1", {}, rel) == "ts_a@1"


def test_send_ts_aliases_picks_minimum_offset_base():
    subs = [
        ["ts_b@2", ["ts_a@1", "+", 3]],
        ["ts_c@3", ["ts_b@2", "+", 2]],
    ]
    aliases = propagate.send_ts_aliases({"ts_a@1", "ts_b@2", "ts_c@3"}, [], subs)
    assert aliases == {
        "ts_a@1": ("ts_a@1", 0),
        "ts_b@2": ("ts_a@1", 3),
        "ts_c@3": ("ts_a@1", 5),
    }


def test_send_ts_aliases_two_col_gaps():
    gaps = [(0, "ts_b@2", "ts_a@1", -3)]   # ts_b = ts_a + 3
    aliases = propagate.send_ts_aliases({"ts_a@1", "ts_b@2"}, gaps, None)
    assert aliases == {"ts_a@1": ("ts_a@1", 0), "ts_b@2": ("ts_a@1", 3)}


def test_rewrite_ts_slot_composes_intra_offset():
    aliases = {"ts_b@2": ("ts_a@1", 3)}
    assert propagate._rewrite_ts_slot(["ts_b@2", "+", 1], aliases) == ["ts_a@1", "+", 4]
    assert propagate._rewrite_ts_slot("ts_a@1", aliases) == "ts_a@1"


@pytest.mark.skipif(not _DUMP_2100223.is_file(), reason="regression dump not present")
def test_2100223_store_pointer_not_guessed():
    """AS2 write_base at access 542 must not become const 0 via unbound mem_ptr."""
    data = json.loads(_DUMP_2100223.read_text())
    an = Analysis(data, assume_is_valid=False)
    row = an.mem[819]
    assert row.addr_space == 2
    assert not isinstance(row.ptr, int)
    key = keys.recover_key(an, row)
    assert not isinstance(key, keys.Const), f"guessed pointer: {key}"


@pytest.mark.skipif(not _DUMP_2100223.is_file(), reason="regression dump not present")
def test_2100223_step0_no_symbolic_address_space():
    data = json.loads(_DUMP_2100223.read_text())
    an = Analysis(data, assume_is_valid=False)
    assert symbolic_as_ordinals(an.mem) == []


@pytest.mark.skipif(not _DUMP_2103992.is_file(), reason="regression dump not present")
def test_2103992_step0_acceptance():
    data = json.loads(_DUMP_2103992.read_text())
    an = Analysis(data, assume_is_valid=False)
    assert symbolic_as_ordinals(an.mem) == []
    for row in an.mem:
        assert an.kinds.get(row.ordinal) is not None, f"ordinal {row.ordinal}"


@pytest.mark.skipif(not _DUMP_2103993.is_file(), reason="regression dump not present")
def test_is_load_case_split_2103993():
    data = json.loads(_DUMP_2103993.read_text())
    an = Analysis(data, assume_is_valid=False)
    row14 = next(r for r in an.mem if r.ordinal == 14)
    row28 = next(r for r in an.mem if r.ordinal == 28)
    assert row14.addr_space_expr == 2
    assert row28.addr_space_expr == 2
    for ord in (16, 17, 26, 27):
        row = next(r for r in an.mem if r.ordinal == ord)
        assert row.ptr == 44
        assert keys.recover_key(an, row) == keys.Const(44)


@pytest.mark.skipif(not _DUMP_2099828.is_file(), reason="regression dump not present")
def test_2099828_access1_flags_pinned_and_drop_from_pointer():
    data = json.loads(_DUMP_2099828.read_text())
    an = Analysis(data, assume_is_valid=True)
    prop = an._propagation
    flag_cols = (
        "flags__0_1@59",
        "flags__1_1@60",
        "flags__2_1@61",
        "flags__3_1@62",
    )
    for col, val in zip(flag_cols, (0, 0, 0, 1)):
        assert col in prop.pins
        assert prop.pins[col].value == val
    row10 = an.mem[10]
    assert "flags__" not in json.dumps(row10.ptr)
