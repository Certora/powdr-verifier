"""Constant propagation for memory-bus multiplicities."""
import json
from pathlib import Path

import pytest

from src.lens.loader import machine_of
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
    an = _an(cons, [{"id": 1, "mult": "g@1", "args": [1, 8, 0, 0, 0, 0, "t@2"]}])
    assert an.kinds[0].kind == "send"


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
    pins, zeros, _ = propagate.propagate(_an([_bool("x@1"), _add("x@1", -1)]))
    assert pins["x@1"] == 1
    assert propagate.eval_mult(mf, pins, zeros) == P - 1


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


def test_refute_expr_requires_bound_columns():
    """Unbound columns that still affect the value are not guessed."""
    expr = ["ptr@1", "+", "mem@2"]
    pins = {"ptr@1": 8}
    envs = {0: [{"ptr@1": 8, "flags__0_0@3": 0}]}
    assert propagate._refute_expr(expr, pins, envs) is None


def test_refute_expr_zeroes_pinned_factor():
    """Pinned zero eliminates an unbound multiplicand."""
    expr = [["is_load_0@10", "*", "rd_0@11"], "+", "ptr_0@12"]
    pins = {"is_load_0@10": 0, "ptr_0@12": 44}
    envs = {0: [{"is_load_0@10": 0, "ptr_0@12": 44, "flags__0_0@5": 0}]}
    assert propagate._refute_expr(expr, pins, envs) == 44


@pytest.mark.skipif(not _DUMP_2100223.is_file(), reason="regression dump not present")
def test_decoding_index_matches_naive_deciding():
    data = json.loads(_DUMP_2100223.read_text())
    cons = machine_of(data).get("constraints", [])
    index = propagate._DecodingIndex.build(cons)
    cols = propagate._all_constraint_cols({"constraints": cons})
    for is_load in sorted(c for c in cols if c.startswith("is_load_")):
        m = propagate._IS_LOAD_RE.match(is_load)
        if m is None:
            continue
        flag_cols = propagate._flag_cols_for_access(cols, int(m.group(1)))
        if not flag_cols:
            continue
        naive = propagate._deciding_constraints(cons, is_load, flag_cols, {})
        indexed = index.deciding_constraints(is_load, flag_cols)
        assert indexed == naive, is_load


def test_fold_pins_algebraic_identities():
    col = "mem_ptr_limbs__0_1@52"
    assert propagate._fold_pins([0, "+", [1, "*", col]], {}) == col
    assert propagate._fold_pins([col, "+", 0], {}) == col
    assert propagate._fold_pins([col, "-", 0], {}) == col
    assert propagate._fold_pins([[1, "*", col], "*", 1], {}) == col
    assert propagate._fold_pins([0, "-", col], {}) == ["-", col]


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
