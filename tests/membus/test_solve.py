"""Graph solver: inputs / outputs / data-flow matching for AS1."""
import pytest

from src.membus import solve


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
PVA = "rs_aux__base__prev_timestamp_0@7"   # cell 8, access 0 (reads entry)
PVB = "rs_aux__base__prev_timestamp_1@8"   # cell 8, access 1 (reads send_a)
PVC = "rs_aux__base__prev_timestamp_0@9"   # cell 12, reads entry


def _send(ptr, ts):
    return {"id": 1, "mult": 1, "args": [1, ptr, 0, 0, 0, 0, ts]}


def _recv(ptr, ts):
    return {"id": 1, "mult": -1, "args": [1, ptr, 0, 0, 0, 0, ts]}


def _dump(with_chain=True):
    # cell 8: RMW over 2 accesses -> input recv_a, interior recv_b<-send_a, output send_b.
    # cell 12: read-once/write-once -> input recv_c, output send_c.
    # file order fixes the membus ordinals: 0..5
    bis = [
        _send(8, FS0),    # 0 send_a @ T+0
        _recv(8, PVA),    # 1 recv_a (input)
        _send(8, FS1),    # 2 send_b @ T+3 (output)
        _recv(8, PVB),    # 3 recv_b -> send_a
        _send(12, FS1),   # 4 send_c @ T+3 (output)
        _recv(12, PVC),   # 5 recv_c (input)
    ]
    cons = [
        # R2 recv bounds: from_state - prev_ts - 1 == 0  ->  prev_ts <= from_state - 1
        _add(FS0, _m(-1, PVA), -1),
        _add(FS1, _m(-1, PVB), -1),
        _add(FS0, _m(-1, PVC), -1),
    ]
    if with_chain:
        cons.append(_add(FS1, _m(-1, FS0), -3))   # R1: fs1 = fs0 + 3
    return {"bus_interactions": bis, "constraints": cons}


def _row(sol, ordinal):
    return next(r for r in sol.rows if r.ordinal == ordinal)


def test_inputs_outputs_and_dataflow():
    sol = solve.compute(_dump(), 1, 1)
    assert sol.ts_entry == 0 and sol.ts_exit == 3
    assert sol.n_inputs == 2 and sol.n_outputs == 2
    assert sol.unique is True
    # cell 8: recv_a input, recv_b reads send_a, send_b output
    assert _row(sol, 1).io == "in"
    assert _row(sol, 3).reads_from == 0          # recv_b <- send_a
    assert _row(sol, 0).read_by == [3]           # send_a read by recv_b
    assert _row(sol, 2).io == "out"              # send_b escapes
    # cell 12: recv_c input, send_c output
    assert _row(sol, 5).io == "in"
    assert _row(sol, 4).io == "out"


def test_interior_recv_vtime_is_matched_send_time():
    sol = solve.compute(_dump(), 1, 1)
    # recv_b reads send_a (@T+0), so its solved prev_ts virtual time is send_a's
    assert _row(sol, 3).vtime_int == 0
    assert _row(sol, 1).vtime_int is None        # input recv: prev_ts before entry


def test_per_cell_results():
    sol = solve.compute(_dump(), 1, 1)
    by_key = {c.key: c for c in sol.cells}
    assert by_key[8].n_send == 2 and by_key[8].edges == [(3, 0)] and by_key[8].unique
    assert by_key[8].input_recv == 1 and by_key[8].output_send == 2
    assert by_key[12].n_send == 1 and by_key[12].edges == [] and by_key[12].unique


def test_json_schema_stable():
    d = solve.compute(_dump(), 1, 1).as_dict()
    assert d["address_space"] == 1 and d["ts_entry"] == 0 and d["ts_exit"] == 3
    assert d["unique"] is True and d["n_inputs"] == 2
    assert "cells" in d and "interactions" in d
    assert {"ordinal", "kind", "io", "vtime", "flow", "reads_from"} <= set(d["interactions"][0])


def test_rejects_non_address_space_1():
    with pytest.raises(ValueError, match="only address space 1"):
        solve.compute(_dump(), 1, 2)


def test_rejects_non_constant_keys():
    d = {"bus_interactions": [_send("rs1_x@5", FS0)], "constraints": []}
    with pytest.raises(ValueError, match="non-constant memkeys"):
        solve.compute(d, 1, 1)


def test_rejects_duplicates():
    d = _dump()
    d["bus_interactions"].append(dict(d["bus_interactions"][0]))   # dup of send_a
    with pytest.raises(ValueError, match="duplicated"):
        solve.compute(d, 1, 1)


def test_disabled_interaction_is_marked_not_matched():
    d = _dump()
    # a disabled (mult 0) interaction in AS1: inert — no ts constraint, matches nothing
    d["bus_interactions"].append({"id": 1, "mult": 0, "args": [1, 8, 0, 0, 0, 0, FS0]})
    sol = solve.compute(d, 1, 1)
    assert sol.n_inputs == 2 and sol.n_outputs == 2 and sol.unique is True   # unchanged
    dis = _row(sol, 6)
    assert dis.kind == "disabled" and dis.io == "" and dis.reads_from is None
    assert all(6 not in e for c in sol.cells for e in c.edges)               # never matched


def test_disabled_via_constant_expression_mult():
    # mult == 0 expressed as a column-free expression (not a bare int) -> still disabled
    d = _dump()
    d["bus_interactions"].append({"id": 1, "mult": [1, "-", 1], "args": [1, 8, 0, 0, 0, 0, FS0]})
    sol = solve.compute(d, 1, 1)
    assert sol.n_inputs == 2 and sol.unique is True
    assert _row(sol, 6).kind == "disabled"


def test_rejects_symbolic_mult():
    d = {"bus_interactions": [{"id": 1, "mult": "sel@5", "args": [1, 8, 0, 0, 0, 0, FS0]}],
         "constraints": []}
    with pytest.raises(ValueError, match="unsupported multiplicity"):
        solve.compute(d, 1, 1)


def test_handles_subtraction_in_gap_constraint():
    # powdr can emit the R1 gap as `fs1 - (fs0 + 3)` instead of `fs1 + (-1)fs0 - 3`
    d = _dump(with_chain=False)
    d["constraints"].append([FS1, "-", [FS0, "+", 3]])
    sol = solve.compute(d, 1, 1)        # must parse the '-' form -> ts_entry well defined
    assert sol.ts_exit == 3 and sol.unique is True


def test_recv_bound_from_range_check_arg():
    # post-`inlining`: the LessThan gadget lives in a range-check (id-3) ARG, not a
    # constraint, and sends are `from_state_0 + offset` in the bus args. solve must
    # recover the order from args and the recv bound from the range-check arg.
    fs = "from_state__timestamp_0@1"
    pv = "aux__base__prev_timestamp_0@7"
    limb = "aux__base__timestamp_lt_aux__lower_decomp__0_0@8"
    # arg = 15360*pv + 15360*limb + 15360 - 15360*fs  (range-checked to 12 bits;
    # 15360 >= 2^12 forces the inner combo to 0 -> pv <= fs - 1)
    arg = [_add(_m(15360, pv), _m(15360, limb), 15360), "-", _m(15360, fs)]
    d = {
        "bus_interactions": [
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, [fs, "+", 5]]},   # send @ T+5
            {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, pv]},            # recv (input)
            {"id": 3, "mult": 1, "args": [arg, 12]},                          # relocated R2
        ],
        "constraints": [],
    }
    sol = solve.compute(d, 1, 1)
    assert sol.ts_entry == 0 and sol.ts_exit == 5
    assert sol.n_inputs == 1 and sol.n_outputs == 1 and sol.unique is True
    assert _row(sol, 1).io == "in"      # recv reads entry (pv <= fs-1 = before ts_entry)
    assert _row(sol, 0).io == "out"     # the lone send escapes


def test_assume_is_valid_resolves_selector_gated_mult():
    # final exported APC: every interaction gated by the global is_valid selector
    fs = "from_state__timestamp_0@1"
    pv = "aux__base__prev_timestamp_0@7"
    limb = "aux__base__timestamp_lt_aux__lower_decomp__0_0@8"
    iv = "is_valid@99"
    arg = [_add(_m(15360, pv), _m(15360, limb), 15360), "-", _m(15360, fs)]
    d = {
        "bus_interactions": [
            {"id": 1, "mult": iv, "args": [1, 8, 0, 0, 0, 0, [fs, "+", 5]]},   # send = is_valid
            {"id": 1, "mult": ["-", iv], "args": [1, 8, 0, 0, 0, 0, pv]},      # recv = -is_valid
            {"id": 3, "mult": 1, "args": [arg, 12]},
        ],
        "constraints": [],
    }
    sol = solve.compute(d, 1, 1)                        # default: assume is_valid == 1
    assert sol.assumed_is_valid is True
    assert sol.n_inputs == 1 and sol.n_outputs == 1 and sol.unique is True
    assert _row(sol, 1).io == "in" and _row(sol, 0).io == "out"
    with pytest.raises(ValueError, match="unsupported multiplicity"):
        solve.compute(d, 1, 1, assume_is_valid=False)   # opt out -> refuse


def test_per_instruction_is_valid_not_assumed():
    # is_valid_<K> (per-instruction, early passes) is NOT the global selector
    from src.membus import solve as _s
    assert _s._kind_assuming_is_valid("is_valid@99") == "send"
    assert _s._kind_assuming_is_valid(["-", "is_valid@99"]) == "recv"
    assert _s._kind_assuming_is_valid("is_valid_0@27") is None          # per-instruction
    assert _s._kind_assuming_is_valid(["opcode_add_flag_0@31", "+", "is_valid@99"]) is None


def test_rejects_unresolved_ts_base():
    # no R1 chain -> fs1's offset from the base is unknown -> ts_entry not well defined
    with pytest.raises(ValueError, match="offsets from a fixed base"):
        solve.compute(_dump(with_chain=False), 1, 1)
