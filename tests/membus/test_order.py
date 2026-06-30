"""Timestamp-order deduction (R0/R1/R2)."""
from src.membus import order


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
PV = "read_data_aux__base__prev_timestamp_0@7"
DEC = "x_lower_decomp__0_0@8"


def test_r1_chain_r2_bound_r0_nonneg():
    dump = {"bus_interactions": [], "constraints": [
        _add(FS1, _m(-1, FS0), -3),                 # fs1 = fs0 + 3  -> edge fs0 -> fs1
        _add(FS0, _m(-1, PV), -1, _m(-1, DEC)),     # fs0 - pv - 1 - dec == 0 -> pv < fs0
    ]}
    edges, recv_bound, nonneg = order.deduce(dump)
    assert (FS0, FS1) in edges
    assert PV in recv_bound and recv_bound[PV][0] == FS0
    assert DEC in nonneg                            # R0: lower_decomp is >= 0
    assert order.total_order(dump, edges) == [FS0, FS1]


def test_linterms_nonlinear_is_none():
    assert order.linterms(["a@1", "*", "b@2"]) is None       # col*col
    assert order.linterms(_add("a@1", 5)) == ({"a@1": 1}, 5)


def test_ts_col_and_access_index():
    assert order.ts_col(_add(FS0, 2)) == FS0        # from_state + offset
    assert order.access_index(FS1) == 1
    assert order.is_fs(FS0) and order.is_prev(PV)
