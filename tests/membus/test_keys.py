"""Memory key recovery and alias classification."""
from src.membus import keys
from src.membus.rules import Analysis


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


def _key(dump, ptr):
    d = dict(dump)
    d["bus_interactions"] = list(d.get("bus_interactions", [])) + [
        {"id": 1, "mult": 1, "args": [2, ptr, 0, 0, 0, 0, "ts@1"]}]
    an = Analysis(d)
    return keys.recover_key(an, an.mem[-1])


def test_constant_key():
    assert _key({"constraints": []}, 8) == keys.Const(8)


def test_unresolved_symbolic_key():
    ptr = ["mem_ptr_limbs__0_5@9", "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert isinstance(_key({"constraints": []}, ptr), keys.Unresolved)


def _gadget_dump(limb, rs0="rs1_data__0_0@3", rs1c="rs1_data__1_0@4",
                 range_check=True, base_bounded=True, limb_bits=14):
    # low-limb gadget: (Y + c)*(Y + c - 1) == 0, c = -1228800 = -30720*40
    f = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228800)
    g = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228801)
    bis = []
    if range_check:
        bis.append({"id": 3, "mult": 1, "args": [limb, limb_bits]})  # limb range-checked
    if base_bounded:
        # base bytes are data of a memory-bus READ (a recv) -> bytes by the
        # membus-byte assumption. (Send data is NOT covered by the assumption.)
        bis.append({"id": 1, "mult": -1, "args": [1, 99, rs0, rs1c, "z0@1", "z1@2", "t@3"]})
    return {"constraints": [[f, "*", g]], "bus_interactions": bis}


PTR = ["mem_ptr_limbs__0_5@9", "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
LIMB = "mem_ptr_limbs__0_5@9"


def test_base_offset_recovery_is_modular():
    # the gadget's other root (the 16-bit carry) is feasible within the window:
    # the recovered identity is mod 2^16, never exact.
    k = _key(_gadget_dump(LIMB), PTR)
    assert k == keys.BaseOffset("rs1_0", 40, mod=65536)
    assert str(k) == "rs1_0+40"                       # label format unchanged


def test_offset_canonicalized_mod():
    # pointer-level constant folds into the offset and reduces mod 2^16
    ptr = [PTR, "+", 65536 + 4]
    assert _key(_gadget_dump(LIMB), ptr) == keys.BaseOffset("rs1_0", 44, mod=65536)


def test_unranged_limb_is_unresolved():
    # limb NOT range-checked -> integer-root pick unjustified -> declined
    assert isinstance(_key(_gadget_dump(LIMB, range_check=False), PTR), keys.Unresolved)


def test_send_data_does_not_bound_base():
    # base bytes appearing only as SEND data are not covered by the membus-byte
    # assumption (reads are assumed, writes are the circuit's burden) -> declined
    d = _gadget_dump(LIMB, base_bounded=False)
    d["bus_interactions"].append(
        {"id": 1, "mult": 1, "args": [1, 99, "rs1_data__0_0@3", "rs1_data__1_0@4",
                                      "z0@1", "z1@2", "t@3"]})
    assert isinstance(_key(d, PTR), keys.Unresolved)


def test_unbounded_base_is_unresolved():
    # base bytes neither range-checked nor membus recv data -> not bounded -> declined
    assert isinstance(_key(_gadget_dump(LIMB, base_bounded=False), PTR), keys.Unresolved)


def test_wide_limb_is_unresolved():
    # limb range-checked but to 31 bits -> window >= p -> could wrap -> declined
    assert isinstance(_key(_gadget_dump(LIMB, limb_bits=31), PTR), keys.Unresolved)


def test_wide_limb_boundary_resolves():
    # 30-bit limb: window = 2^30 + 256 + 256*256 + 40 < p -> still resolves (mod 2^16).
    assert _key(_gadget_dump(LIMB, limb_bits=30), PTR) == \
        keys.BaseOffset("rs1_0", 40, mod=65536)


def test_classify_address_space():
    assert keys.classify_address_space([keys.Const(8), keys.Const(12)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4, 65536), keys.BaseOffset("rs1_0", 8, 65536)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4, 65536), keys.BaseOffset("read_9", 0, 65536)])[0] is False
    # mixed moduli: offsets are not comparable -> not determined
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4, 65536), keys.BaseOffset("rs1_0", 8, None)])[0] is False
    assert keys.classify_address_space([keys.Unresolved("x")])[0] is False
