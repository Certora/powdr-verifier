"""Abstract-order .bus extraction + removed-set diff."""
import pytest

from src.membus import extract
from src.membus.busmodel import find_duplicates, memory_rows, removed_rows


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
PV = "read_data_aux__base__prev_timestamp_1@5"


def _chain_dump():
    """Two AS1 accesses to address 8 (constant key) + their order constraints."""
    return {
        "bus_interactions": [
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS0]},
            {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, PV]},
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, [FS1, "+", 1]]},
        ],
        "constraints": [
            _add(FS1, _m(-1, FS0), -3),      # fs0 -> fs1
            _add(FS1, _m(-1, PV), -1),       # pv < fs1
        ],
    }


def test_build_dict_json_shape():
    model = extract.build_dict(_chain_dump(), 1, 1, None)
    pub = extract.extract_json(model)
    assert len(pub["interactions"]) == 3
    ts = [r["abstract_ts"] for r in pub["interactions"]]
    assert len(set(ts)) == len(ts)
    assert pub["order_edges"]
    assert all(r["alias_class"] == 0 for r in pub["interactions"])
    assert pub["interactions"][0]["alias_determined"] is True
    assert pub["interactions"][0]["address_space"] == "1"
    assert pub["interactions"][0]["key"] == "const 8"
    assert pub["unordered"] == []            # everything justified


def test_edges_are_justified():
    # send@T+0, send@T+4 (fs1+1), recv pv <= fs1-1 = T+2 -> recv < send@T+4 only.
    model = extract.build_dict(_chain_dump(), 1, 1, None)
    sym = {r["ordinal"]: r["abstract_ts"] for r in model["interactions"]}
    edges = {(e["lhs"], e["rhs"]) for e in model["order_edges"]}
    assert (sym[0], sym[2]) in edges                       # send chain T+0 < T+4
    assert (sym[1], sym[2]) in edges                       # recv (<=T+2) < send @T+4
    assert (sym[1], sym[0]) not in edges                   # NOT before send @T+0
    assert all("(" not in lhs for lhs, _ in edges)


def test_unbounded_recv_gets_no_edge_and_is_reported():
    d = _chain_dump()
    d["constraints"] = [_add(FS1, _m(-1, FS0), -3)]        # drop the R2 bound
    model = extract.build_dict(d, 1, 1, None)
    sym = {r["ordinal"]: r["abstract_ts"] for r in model["interactions"]}
    assert all(e["lhs"] != sym[1] for e in model["order_edges"])
    assert [u["abstract_ts"] for u in model["unordered"]] == [sym[1]]
    txt = extract.format_bus(model)
    assert "UNORDERED" in txt


def test_extract_unary_minus_mult():
    d = {
        "bus_interactions": [
            {"id": 1, "mult": ["-", 1], "args": [1, 8, 0, 0, 0, 0, FS0]},
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, [FS1, "+", 1]]},
        ],
        "constraints": [_add(FS1, _m(-1, FS0), -3)],
    }
    txt = extract.build(d, 1, 1, None)
    assert "0: -1," in txt
    assert "1: 1," in txt


def test_extract_emits_abstract_bus():
    txt = extract.build(_chain_dump(), 1, 1, None)
    assert txt.startswith("MEM")
    assert "CONSTRAINTS" in txt
    rows = [ln for ln in txt.splitlines() if ln[:1].isdigit() and ":" in ln]
    assert len(rows) == 3
    # abstract timestamps only — no raw from_state in the MEM rows
    assert all("from_state" not in r for r in rows)
    assert all(", ts" in r for r in rows)


def test_extract_rejects_duplicate_interactions():
    # two identical interactions (same mult + args, including timestamp) -> ill-defined
    dup = {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS0]}
    d = {"bus_interactions": [dup, dict(dup)], "constraints": []}
    with pytest.raises(ValueError, match="duplicated memory interaction"):
        extract.build(d, 1, 1, None)


def test_find_duplicates():
    a = {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "t@1"]}
    b = {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, "t@1"]}   # differs by mult
    rows = memory_rows({"bus_interactions": [a, b], "constraints": []})
    assert find_duplicates(rows) == []                             # distinct
    rows2 = memory_rows({"bus_interactions": [a, dict(a)], "constraints": []})
    dups = find_duplicates(rows2)
    assert dups and dups[0][1] == 2


def test_removed_set_is_multiset_diff():
    a = {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "t@1"]}
    b = {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, "t@2"]}
    pre_rows = memory_rows({"bus_interactions": [a, b], "constraints": []})
    post_rows = memory_rows({"bus_interactions": [a], "constraints": []})
    removed = removed_rows(pre_rows, post_rows)
    assert [r.ordinal for r in removed] == [1]
    assert removed[0].mult == -1
