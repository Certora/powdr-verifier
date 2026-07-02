"""Timestamp-order deduction: Gap/RecvUpper facts, verified total order."""
from src.membus import order
from src.membus.linform import linform
from src.membus.rules import Analysis


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
FS2 = "from_state__timestamp_2@3"
PV = "read_data_aux__base__prev_timestamp_0@7"
DEC = "x_lower_decomp__0_0@8"


def _an(cons, bis=()):
    return Analysis({"bus_interactions": list(bis), "constraints": cons})


def test_gap_and_recv_upper_facts():
    an = _an(
        [
            _add(FS1, _m(-1, FS0), -3),                 # fs1 = fs0 + 3
            _add(FS0, _m(-1, PV), -1, _m(-1, DEC)),     # fs0 - pv - 1 - dec == 0
        ],
        bis=[{"id": 3, "mult": 1, "args": [DEC, 17]}],   # dec width known
    )
    assert [(g.earlier, g.later, g.gap) for g in an.gaps] == [(FS0, FS1, 3)]
    ups = an.recv_uppers[PV]
    assert len(ups) == 1 and ups[0].fs == FS0 and ups[0].const == -1
    assert order.total_send_order(an) == [FS0, FS1]
    assert order.send_offsets(an) == {FS0: 0, FS1: 3}


def test_r2_declines_unbounded_limb():
    # limb has no range check with a known width -> no window -> no fact
    an = _an([_add(FS0, _m(-1, PV), -1, _m(-1, DEC))])
    assert PV not in an.recv_uppers


def test_partial_order_is_not_linearized():
    # fs0 < fs1 known; fs2 unordered -> NO total order (old code lex-sorted it in)
    an = _an([_add(FS1, _m(-1, FS0), -3)],
             bis=[{"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS2]}])
    assert order.total_send_order(an) is None
    assert set(order.send_offsets(an).values()) == {None}


def test_transitive_only_gap_leaves_offset_unknown():
    # fs0<fs1 and fs0<fs2 with fs1<fs2: chain total, but fs1->fs2 gap direct
    an = _an([
        _add(FS1, _m(-1, FS0), -3),
        _add(FS2, _m(-1, FS1), -2),
    ])
    assert order.total_send_order(an) == [FS0, FS1, FS2]
    assert order.send_offsets(an) == {FS0: 0, FS1: 3, FS2: 5}


def test_linform_nonlinear_is_none():
    assert linform(["a@1", "*", "b@2"]) is None          # col*col
    lf = linform(_add("a@1", 5))
    assert lf.coeffs == (("a@1", 1),) and lf.const == 5


def test_linform_canonical_mod_p():
    # accumulated constants reduce to the canonical signed residue
    p = 2013265921
    lf = linform(_add(1006632960, 1006632961))           # sums to exactly p == 0
    assert lf is not None and lf.const == 0 and lf.is_const
    lf2 = linform(_m(p - 1, "a@1"))                       # coeff p-1 == -1
    assert lf2.coeffs == (("a@1", -1),)


def test_ts_col_and_access_index():
    assert order.ts_col(_add(FS0, 2)) == FS0        # from_state + offset
    assert order.access_index(FS1) == 1
    from src.membus import naming
    assert naming.is_fs(FS0) and naming.is_prev(PV)
