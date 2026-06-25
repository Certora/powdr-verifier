"""Renderer output: stable JSON keys and plain text that carries the numbers."""
import json

from src.lens.metrics import NEG_ONE, DumpDiff, DumpStats
from src.lens.render import (
    JSON, PLAIN, Target, render_compare, render_memkeys, render_show,
)


def _machine(constraints, bus=None):
    return {
        "constraints": constraints,
        "bus_interactions": bus or [],
        "derived_columns": [],
    }


def _stats(n_extra_constraint=False):
    cons = [["f@0", "*", ["f@0", "-", 1]]]
    if n_extra_constraint:
        cons.append("g@1")
    bus = [{"id": 1, "mult": 1, "args": ["a@0"]},
           {"id": 1, "mult": NEG_ONE, "args": []}]
    return DumpStats.from_data(_machine(cons, bus), {"1": "Memory"})


def test_show_json_schema():
    s = _stats(n_extra_constraint=True)
    t = Target("keccak", "111", "011_memory", "p.json")
    out = json.loads(render_show(s, t, JSON))
    for key in ("target", "n_constraints", "n_bus_interactions",
                "n_derived_columns", "distinct_columns", "degree",
                "degree_hist", "nodes", "depth", "op_hist", "buses",
                "derived_forms"):
        assert key in out, f"missing {key}"
    assert out["n_constraints"] == 2
    assert out["buses"][0]["label"] == "Memory"
    assert set(out["buses"][0]) == {
        "id", "label", "count", "send", "recv", "sym", "other", "args_nodes",
        "key_sym",
    }


def test_show_plain_has_numbers():
    s = _stats()
    t = Target("keccak", "111", "011_memory", "p.json")
    text = render_show(s, t, PLAIN)
    assert "constraints\t1" in text
    assert "bus\t1\tMemory\t2\t1\t1\t" in text


def test_compare_json_deltas():
    a, b = _stats(), _stats(n_extra_constraint=True)
    ta = Target("keccak", "111", "011_memory", "a.json")
    tb = Target("keccak", "111", "016_remove_free", "b.json")
    out = json.loads(render_compare(DumpDiff(a, b), ta, tb, JSON))
    assert out["scalars"]["n_constraints"] == {"a": 1, "b": 2, "delta": 1}
    assert out["buses"][0]["delta"] == 0


def test_compare_plain_shows_delta():
    a, b = _stats(), _stats(n_extra_constraint=True)
    ta = Target("keccak", "111", "011", "a.json")
    tb = Target("keccak", "111", "016", "b.json")
    text = render_compare(DumpDiff(a, b), ta, tb, PLAIN)
    assert "n_constraints\t1\t2\t+1" in text


def _mem_machine():
    return {"bus_interactions": [
        {"id": 1, "mult": 1, "args": [2, ["p@0", "+", 1], "d@1", "ts@2"]},  # sym
        {"id": 1, "mult": 1, "args": [2, ["p@0", "+", 1], "d@3", "ts@4"]},  # same key
        {"id": 1, "mult": 1, "args": [1, 40, "d@5", "ts@6"]},               # concrete
        {"id": 3, "mult": 1, "args": ["x@0", 17]},                          # not memory
    ]}


def test_memkeys_symbolic_only_grouping():
    out = json.loads(render_memkeys(_mem_machine(), "k", "1", "050", True, 50, JSON))
    assert out["memory"] == {"total": 3, "symbolic": 2}
    assert len(out["keys"]) == 1                 # one distinct symbolic key
    assert out["keys"][0]["count"] == 2          # two interactions share it
    assert out["keys"][0]["symbolic"] is True
    assert out["keys"][0]["pointer"] == "(p@0 + 1)"


def test_memkeys_all_includes_concrete():
    out = json.loads(render_memkeys(_mem_machine(), "k", "1", "050", False, 50, JSON))
    assert len(out["keys"]) == 2                 # symbolic + concrete
    text = render_memkeys(_mem_machine(), "k", "1", "050", True, 50, PLAIN)
    assert "2 of 3 interactions symbolic" in text
