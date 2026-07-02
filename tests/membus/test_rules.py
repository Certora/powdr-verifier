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
    assert Assumption.TS_BOUND in ups[0].assumptions


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

def test_r2_constraint_requires_bounded_limbs():
    con = _add(FS, _m(-1, PV), -1, _m(-1, LIMB))
    assert PV not in _an([con]).recv_uppers                    # limb unbounded
    an = _an([con], bis=[{"id": 3, "mult": 1, "args": [LIMB, 17]}])
    assert [u.const for u in an.recv_uppers[PV]] == [-1]


def test_r2_multiple_bounds_all_kept():
    c1 = _add(FS, _m(-1, PV), -1)
    c2 = _add(FS, _m(-1, PV), -4)
    an = _an([c1, c2])
    assert sorted(u.const for u in an.recv_uppers[PV]) == [-4, -1]


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
