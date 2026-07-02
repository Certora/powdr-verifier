"""memstats / meminfo computation and JSON schema."""
import json

from src.membus import meminfo, memstats, render
from src.membus.render import JSON, Target


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0, FS1 = "from_state__timestamp_0@1", "from_state__timestamp_1@2"
PV = "read_data_aux__base__prev_timestamp_1@5"


def _dump():
    # AS1, two constant addresses (8, 12); a recv reading address 8.
    return {
        "bus_interactions": [
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, FS0]},
            {"id": 1, "mult": -1, "args": [1, 8, 0, 0, 0, 0, PV]},
            {"id": 1, "mult": 1, "args": [1, 12, 0, 0, 0, 0, [FS1, "+", 1]]},
            {"id": 2, "mult": 1, "args": ["pc@9", "t@9"]},   # non-memory, ignored
        ],
        "constraints": [_add(FS1, _m(-1, FS0), -3), _add(FS1, _m(-1, PV), -1)],
    }


def test_stats_address_space_split():
    st = memstats.compute(_dump(), 1)
    assert st.n_memory == 3
    assert len(st.address_spaces) == 1
    a = st.address_spaces[0]
    assert a.addr_space == "1" and a.count == 3
    assert a.send == 2 and a.recv == 1
    assert a.determined is True and a.distinct_keys == 2   # addresses 8 and 12
    assert st.sends_ordered and st.recvs_bounded


def test_stats_json_schema():
    st = memstats.compute(_dump(), 1)
    out = json.loads(render.render_stats(st, Target("g", "b", "s", "p"), JSON))
    assert out["n_memory"] == 3
    assert out["preconditions"]["sends_totally_ordered"] is True
    assert out["preconditions"]["no_duplicates"] is True
    assert out["preconditions"]["duplicates"] == 0
    assert "address_spaces" in out and "alias_determined" in out["address_spaces"][0]


def test_stats_counts_duplicates():
    d = _dump()
    d["bus_interactions"].append(dict(d["bus_interactions"][0]))   # exact dup of first
    st = memstats.compute(d, 1)
    assert st.duplicates == 1
    out = json.loads(render.render_stats(st, Target("g", "b", "s", "p"), JSON))
    assert out["preconditions"]["no_duplicates"] is False


def test_info_keys_and_classes():
    rows = meminfo.compute(_dump(), 1)
    assert [r.key for r in rows] == ["const 8", "const 8", "const 12"]
    # the two address-8 interactions share an alias class; address 12 differs
    assert rows[0].alias_class == rows[1].alias_class != rows[2].alias_class
    out = json.loads(render.render_info(rows, Target("g", "b", "s", "p"), JSON))
    assert len(out["interactions"]) == 3


def test_stats_warns_on_symbolic_as():
    d = _dump()
    d["bus_interactions"].append({"id": 1, "mult": 1, "args": ["mem_as@9", 8, 0, 0, 0, 0, FS0]})
    st = memstats.compute(d, 1)
    assert st.symbolic_as == 1
    assert "WARNING" in render.render_stats(st, Target("g", "b", "s", "p"), render.PLAIN)
    j = json.loads(render.render_stats(st, Target("g", "b", "s", "p"), JSON))
    assert j["preconditions"]["solved_as_form"] is False
    assert j["preconditions"]["symbolic_as"] == 1


def test_info_warns_on_symbolic_as():
    rows = meminfo.compute(_dump(), 1)
    out = render.render_info(rows, Target("g", "b", "s", "p"), render.PLAIN, symbolic_as=2)
    assert "WARNING" in out
    j = json.loads(render.render_info(rows, Target("g", "b", "s", "p"), JSON, symbolic_as=2))
    assert j["symbolic_as"] == 2 and j["solved_as_form"] is False
