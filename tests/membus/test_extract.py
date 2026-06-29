"""Abstract-order .bus extraction + removed-set diff."""
from src.membus import extract
from src.membus.busfmt import removed_memory_bis


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


def test_extract_emits_abstract_bus():
    txt = extract.build(_chain_dump(), 1, 1, None)
    assert txt.startswith("MEM")
    assert "CONSTRAINTS" in txt
    rows = [ln for ln in txt.splitlines() if ln[:1].isdigit() and ":" in ln]
    assert len(rows) == 3
    # abstract timestamps only — no raw from_state in the MEM rows
    assert all("from_state" not in r for r in rows)
    assert all(", ts" in r for r in rows)


def test_removed_set_is_multiset_diff():
    a = {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "t@1"]}
    b = {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, "t@2"]}
    pre = {"bus_interactions": [a, b], "constraints": []}
    post = {"bus_interactions": [a], "constraints": []}
    removed = removed_memory_bis(pre, post, 1)
    assert removed == [b]
