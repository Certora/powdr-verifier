"""Memory key recovery and alias classification."""
from src.membus import keys


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


def _bi(ptr):
    return {"id": 1, "mult": 1, "args": [2, ptr, 0, 0, 0, 0, "ts@1"]}


def test_constant_key():
    bi = {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "ts@1"]}
    assert keys.recover_key({"constraints": []}, bi) == keys.Const(8)


def test_unresolved_symbolic_key():
    ptr = ["mem_ptr_limbs__0_5@9", "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    k = keys.recover_key({"constraints": []}, _bi(ptr))
    assert isinstance(k, keys.Unresolved)


def _gadget_dump(limb, rs0="rs1_data__0_0@3", rs1c="rs1_data__1_0@4",
                 range_check=True, base_bounded=True, limb_bits=14):
    # low-limb gadget: (Y + c)*(Y + c - 1) == 0, c = -1228800 = -30720*40
    f = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228800)
    g = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228801)
    bis = []
    if range_check:
        bis.append({"id": 3, "mult": 1, "args": [limb, limb_bits]})  # limb range-checked
    if base_bounded:
        # base bytes are data of a memory-bus (id 1) read -> bounded (bytes)
        bis.append({"id": 1, "mult": 1, "args": [1, 99, rs0, rs1c, "z0@1", "z1@2", "t@3"]})
    return {"constraints": [[f, "*", g]], "bus_interactions": bis}


def test_base_offset_recovery():
    limb = "mem_ptr_limbs__0_5@9"
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert keys.recover_key(_gadget_dump(limb), _bi(ptr)) == keys.BaseOffset("rs1_0", 40)


def test_unranged_limb_is_unresolved():
    # limb NOT range-checked -> integer-root pick unjustified -> declined
    limb = "mem_ptr_limbs__0_5@9"
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert isinstance(keys.recover_key(_gadget_dump(limb, range_check=False), _bi(ptr)),
                      keys.Unresolved)


def test_unbounded_base_is_unresolved():
    # base bytes neither range-checked nor membus data -> not bounded -> declined
    limb = "mem_ptr_limbs__0_5@9"
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert isinstance(keys.recover_key(_gadget_dump(limb, base_bounded=False), _bi(ptr)),
                      keys.Unresolved)


def test_wide_limb_is_unresolved():
    # limb range-checked but to 31 bits -> window 2^31 + ... >= p -> could wrap ->
    # integer root not provably unique -> declined.
    limb = "mem_ptr_limbs__0_5@9"
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert isinstance(keys.recover_key(_gadget_dump(limb, limb_bits=31), _bi(ptr)),
                      keys.Unresolved)


def test_wide_limb_boundary_resolves():
    # 30-bit limb: window = 2^30 + 256 + 256*256 + 40 < p -> still resolves.
    limb = "mem_ptr_limbs__0_5@9"
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert keys.recover_key(_gadget_dump(limb, limb_bits=30), _bi(ptr)) == \
        keys.BaseOffset("rs1_0", 40)


def test_classify_address_space():
    assert keys.classify_address_space([keys.Const(8), keys.Const(12)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4), keys.BaseOffset("rs1_0", 8)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4), keys.BaseOffset("read_9", 0)])[0] is False
    assert keys.classify_address_space([keys.Unresolved("x")])[0] is False
