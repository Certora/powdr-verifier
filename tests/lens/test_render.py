"""Renderer output: stable JSON keys and plain text that carries the numbers."""
import json

from src.lens.metrics import NEG_ONE, DumpDiff, DumpStats
from src.lens.render import JSON, PLAIN, Target, render_compare, render_show


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
