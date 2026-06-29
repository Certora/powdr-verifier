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


def test_base_offset_recovery():
    limb = "mem_ptr_limbs__0_5@9"
    rs0, rs1c = "rs1_data__0_0@3", "rs1_data__1_0@4"
    # low-limb gadget: (Y + c)*(Y + c - 1) == 0, c = -1228800 = -30720*40
    f = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228800)
    g = _add(_m(-30720, rs0), _m(-7864320, rs1c), _m(30720, limb), -1228801)
    dump = {"constraints": [[f, "*", g]]}
    ptr = [limb, "+", [65536, "*", "mem_ptr_limbs__1_5@10"]]
    assert keys.recover_key(dump, _bi(ptr)) == keys.BaseOffset("rs1_0", 40)


def test_classify_address_space():
    assert keys.classify_address_space([keys.Const(8), keys.Const(12)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4), keys.BaseOffset("rs1_0", 8)])[0] is True
    assert keys.classify_address_space(
        [keys.BaseOffset("rs1_0", 4), keys.BaseOffset("read_9", 0)])[0] is False
    assert keys.classify_address_space([keys.Unresolved("x")])[0] is False
