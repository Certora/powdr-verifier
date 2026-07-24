"""Extraction-rule side conditions — regression tests for the review findings."""
from src.lens.normalize import BABYBEAR_PRIME as P

from src.membus.facts import Assumption
from src.membus.rules import Analysis


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS = "from_state__timestamp_0@1"
PV = "aux__base__prev_timestamp_0@7"
LIMB = "aux__lower_decomp__0_0@8"


def _an(cons=(), bis=()):
    return Analysis({"constraints": list(cons), "bus_interactions": list(bis)})


# -- R0: bounds --------------------------------------------------------------

def test_compound_range_arg_bounds_no_column():
    # x - y range-checked bounds the VALUE x-y, not x or y individually
    an = _an(bis=[{"id": 3, "mult": 1, "args": [["x@1", "-", "y@2"], 16]}])
    assert "x@1" not in an.bounds and "y@2" not in an.bounds


def test_bare_and_scaled_range_args_bound():
    inv = pow(30720, -1, P)     # scaled encoding: col/30720 in [0, 2^14)
    an = _an(bis=[
        {"id": 3, "mult": 1, "args": ["x@1", 16]},
        {"id": 3, "mult": 1, "args": [[inv, "*", "y@2"], 14]},
    ])
    assert an.bounds["x@1"].hi == 1 << 16
    assert an.bounds["y@2"].hi == 30720 * (1 << 14)


def test_disabled_range_check_emits_no_bound():
    # A range-check whose multiplicity is provably zero (gate pinned to 0 by a
    # single-column constraint) is not sent and constrains nothing, so its arg
    # must NOT be bounded — else a false Bound would certify unsat (the range
    # source is asserted unconditionally). An active row still bounds its arg.
    an = _an(cons=[["gate@1", "-", 0]],
             bis=[{"id": 3, "mult": "gate@1", "args": ["aux@2", 17]}])
    assert "aux@2" not in an.bounds
    an2 = _an(bis=[{"id": 3, "mult": 1, "args": ["aux@2", 17]}])
    assert an2.bounds["aux@2"].hi == 1 << 17


def test_byte_bound_is_recv_only_and_assumed():
    recv = {"id": 1, "mult": -1, "args": [1, 8, "r0@1", 0, 0, 0, PV]}
    send = {"id": 1, "mult": 1, "args": [1, 8, "s0@2", 0, 0, 0, FS]}
    an = _an(bis=[recv, send])
    assert an.bounds["r0@1"].hi == 256
    assert Assumption.MEMBUS_BYTE in an.bounds["r0@1"].assumptions
    assert "s0@2" not in an.bounds           # send data: circuit's burden, not assumed


# -- R2 range-check form: the sign of the scale factor decides ---------------

def _r2_bus(coeff_fs):
    """Range-checked arg with the R2 shape; coeff_fs = the fs coefficient."""
    arg = _add(_m((-coeff_fs) % P, PV), _m((-coeff_fs) % P, LIMB), (-coeff_fs) % P,
               _m(coeff_fs % P, FS))
    return _an(bis=[
        {"id": 3, "mult": 1, "args": [arg, 12]},
        {"id": 3, "mult": 1, "args": [LIMB, 17]},
        {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, [FS, "+", 5]]},
        {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, PV]},
    ])


def test_r2_bus_sound_sign_accepted():
    # cf = -15360 == 2^-17 (mod p): admitted solutions are k = 2^17*r >= 0 -> sound
    an = _r2_bus(-15360)
    ups = an.recv_uppers.get(PV, [])
    assert len(ups) == 1 and ups[0].const == -1
    assert Assumption.TS_BOUND in ups[0].all_assumptions()   # via the slot Bound premises


def test_r2_bus_mirrored_sign_rejected():
    # cf = +15360 == -2^-17 (mod p): admits k = -2^17*r < 0 inside the window,
    # where the conclusion is FALSE. The old divisibility test accepted this.
    an = _r2_bus(15360)
    assert PV not in an.recv_uppers


def test_r2_bus_unbounded_limb_rejected():
    an = _r2_bus(-15360)
    an2 = Analysis({"constraints": [],
                    "bus_interactions": [b for b in an.machine["bus_interactions"]
                                         if b["args"] != [LIMB, 17]]})
    assert PV not in an2.recv_uppers


# -- R2 constraint form -------------------------------------------------------

_MEM_ROWS = [  # seed the positional ts domain: FS is a send clock, PV a recv witness
    {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS]},
    {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, PV]},
]


def test_r2_constraint_requires_bounded_limbs():
    con = _add(FS, _m(-1, PV), -1, _m(-1, LIMB))
    assert PV not in _an([con], bis=_MEM_ROWS).recv_uppers     # limb unbounded
    an = _an([con], bis=[*_MEM_ROWS, {"id": 3, "mult": 1, "args": [LIMB, 17]}])
    assert [u.const for u in an.recv_uppers[PV]] == [-1]


def test_r2_multiple_bounds_all_kept():
    c1 = _add(FS, _m(-1, PV), -1)
    c2 = _add(FS, _m(-1, PV), -4)
    an = _an([c1, c2], bis=_MEM_ROWS)
    assert sorted(u.const for u in an.recv_uppers[PV]) == [-4, -1]


def _bool(col):
    return [col, "*", [col, "+", -1]]


def test_r2_constraint_gated_by_pinned_selector():
    # sel * (fs - pv - 1) = 0 with sel pinned to 1 -> the LessThan is recognized
    sel = "is_valid@9"
    body = _add(FS, _m(-1, PV), -1)
    con = [sel, "*", body]
    an = _an([_bool(sel), _add(sel, -1), con], bis=_MEM_ROWS)
    assert [u.const for u in an.recv_uppers[PV]] == [-1]


def test_r2_constraint_gated_by_flag_sum_selector():
    # (a + b) * (fs - pv - 1) = 0 where a + b == 1 is a known zero -> recognized
    a, b = "op_a@9", "op_b@10"
    body = _add(FS, _m(-1, PV), -1)
    con = [_add(a, b), "*", body]
    an = _an([_bool(a), _bool(b), _add(a, b, -1), con], bis=_MEM_ROWS)
    assert [u.const for u in an.recv_uppers[PV]] == [-1]


def test_ts_domain_is_positional_not_named():
    # a slot column with a non-timestamp name is a clock; a from_state-named
    # column NOT in any slot (nor gap-linked) is not
    con = _add("weird@1", _m(-1, "odd@2"), -1)
    an = _an([con], bis=[
        {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "weird@1"]},
        {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, "odd@2"]},
    ])
    assert "weird@1" in an.clock_cols and "odd@2" in an.witness_cols
    assert [u.const for u in an.recv_uppers["odd@2"]] == [-1]
    an2 = _an([], bis=[{"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS]}])
    assert "from_state__timestamp_9@99" not in an2.clock_cols


def test_clock_web_closure_covers_chain_base():
    # fs0 (the chain base) has no memory op of its own; it joins the clock web
    # through the backward gap link and carries the TS_BOUND assumption
    fs0 = "base@1"
    con = _add(FS, _m(-1, fs0), -3)            # FS = fs0 + 3
    an = _an([con], bis=_MEM_ROWS)
    assert fs0 in an.clock_cols
    b = an.bounds[fs0]
    assert Assumption.TS_BOUND in b.assumptions
    assert [(g.later, g.earlier, g.gap) for g in an.gaps] == [(FS, fs0, 3)]


# -- Affine gadget: root refutation / modular identity ------------------------

def _gadget(delta, limb="mem_ptr_limbs__0_5@9", limb_bits=14):
    b0, b1 = "rs1_data__0_0@3", "rs1_data__1_0@4"
    f = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800) % P)
    g = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800 + delta) % P)
    return Analysis({
        "constraints": [[f, "*", g]],
        "bus_interactions": [
            {"id": 3, "mult": 1, "args": [limb, limb_bits]},
            {"id": 1, "mult": -1, "args": [1, 99, b0, b1, "z0@1", "z1@2", "t@3"]},
        ]})


def test_affine_carry_gadget_is_modular():
    # delta = -30720 (i.e. the factors differ by 30720 = the limb's own scale):
    # other root k = -1 -> gcd 1 -> no usable claim.  delta = -1 (the bit
    # gadget): other root k = -65536 -> identity holds mod 2^16.
    an = _gadget(-1)
    d = an.affine("mem_ptr_limbs__0_5@9")
    assert d is not None and d.modulus == 65536 and d.offset == 40


def test_affine_dense_roots_rejected():
    # factors differing by 30720·1 place the other root at k = -1: the gadget
    # admits adjacent integer solutions -> no affine claim at any modulus
    an = _gadget(-30720)
    assert an.affine("mem_ptr_limbs__0_5@9") is None


# -- Bound propagation across two-column equalities ---------------------------

def test_bound_propagates_through_equality():
    # x is range-checked; y == x (a forwarding equality, as the `memory` pass
    # emits after removing the register read whose recv data bounded y)
    an = _an(cons=[_add("x@1", _m(P - 1, "y@2"))],
             bis=[{"id": 3, "mult": 1, "args": ["x@1", 8]}])
    b = an.bounds.get("y@2")
    assert b is not None and (b.lo, b.hi) == (0, 256)
    assert b.premises and b.premises[0].col == "x@1"


def test_bound_propagates_through_offset():
    # y = x + 40: the interval shifts with the offset
    an = _an(cons=[_add("y@2", _m(P - 1, "x@1"), P - 40)],
             bis=[{"id": 3, "mult": 1, "args": ["x@1", 8]}])
    b = an.bounds.get("y@2")
    assert b is not None and (b.lo, b.hi) == (40, 296)


def test_bound_propagation_stops_at_wrap():
    # y = x - 1 with x in [0, 256): the shifted interval leaves [0, p) below
    # (the y = p - 1 wrap branch survives), so no bound may be derived for y
    an = _an(cons=[_add("y@2", _m(P - 1, "x@1"), 1)],
             bis=[{"id": 3, "mult": 1, "args": ["x@1", 8]}])
    assert an.bounds.get("y@2") is None


def test_bound_propagation_restores_gadget_after_forwarding():
    # the flicker scenario: base bytes b0/b1 are NOT membus recv data, but
    # forwarding equalities tie them to range-checked columns -> the affine
    # gadget must still certify
    b0, b1, limb = "rs1_data__0_0@3", "rs1_data__1_0@4", "mem_ptr_limbs__0_5@9"
    f = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800) % P)
    g = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800 - 1) % P)
    an = _an(
        cons=[[f, "*", g],
              _add(b0, _m(P - 1, "w0@11")),       # b0 == w0 (forwarded)
              _add(b1, _m(P - 1, "w1@12"))],      # b1 == w1
        bis=[{"id": 3, "mult": 1, "args": [limb, 14]},
             {"id": 3, "mult": 1, "args": ["w0@11", 8]},
             {"id": 3, "mult": 1, "args": ["w1@12", 8]}])
    d = an.affine(limb)
    assert d is not None and d.modulus == 65536 and d.offset == 40


def test_single_column_constraint_pins_residue():
    # -x + 128 == 0 pins x to exactly 128
    an = _an(cons=[_add(_m(P - 1, "x@1"), 128)])
    b = an.bounds.get("x@1")
    assert b is not None and (b.lo, b.hi) == (128, 129)


def test_gadget_with_constant_pinned_bytes_certifies():
    # the 2106332 residual: base bytes pinned to constants (a constant base
    # address) instead of being range-checked or membus recv data. The tight
    # constant window even excludes the carry root -> the identity is EXACT.
    b0, b1, limb = "rs1_data__0_0@3", "rs1_data__1_0@4", "mem_ptr_limbs__0_5@9"
    f = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800) % P)
    g = _add(_m((-30720) % P, b0), _m((-7864320) % P, b1), _m(30720, limb),
             (-1228800 - 1) % P)
    an = _an(
        cons=[[f, "*", g],
              _add(_m(P - 1, b0), 0),            # b0 == 0
              _add(_m(P - 1, b1), 32)],          # b1 == 32
        bis=[{"id": 3, "mult": 1, "args": [limb, 14]}])
    d = an.affine(limb)
    assert d is not None and d.offset == 40 and d.modulus is None
