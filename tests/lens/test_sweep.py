"""Sweep builder, label abbreviation, and sweep rendering."""
import json

from src.lens import resolve
from src.lens.loader import load_bus_map
from src.lens.render import JSON, PLAIN, render_sweep
from src.lens.sweep import abbrev_label, build_sweep


def _circuit_dump(memory_sym=True):
    # base/circuit dump: block + subs present; a Memory bus with symbolic mult.
    return {
        "block": {"blocks": [{"instructions": [[1]]}]},
        "subs": [[0, 1]],
        "bus_map": {"bus_ids": {"1": "Memory", "3": {"Other": "VariableRangeChecker"}}},
        "machine": {
            "constraints": [["f@0", "*", ["f@0", "-", 1]]],
            "bus_interactions": [
                {"id": 1, "mult": "sel@9" if memory_sym else 1, "args": []},
                {"id": 3, "mult": 1, "args": []},
            ],
            "derived_columns": [],
        },
    }


def _constraints_dump():
    # per-step/constraints dump: top-level constraints, all concrete mults.
    return {
        "constraints": [["f@0", "*", ["f@0", "+", 2013265920]]],
        "bus_interactions": [
            {"id": 1, "mult": 1, "args": []},
            {"id": 1, "mult": 2013265920, "args": []},
        ],
        "derived_columns": [],
    }


def _make_block(tmp_path):
    group = tmp_path / "guest-keccak"
    group.mkdir()
    base = group / "apc_candidate_111_000_unopt.json"
    base.write_text(json.dumps(_circuit_dump()))
    (group / "apc_candidate_111_001_solver.json").write_text(
        json.dumps(_constraints_dump()))
    (group / "apc_candidate_111_002_memory.json").write_text(
        json.dumps(_constraints_dump()))
    return tmp_path


def test_abbrev_label():
    assert abbrev_label("ExecutionBridge") == "EB"
    assert abbrev_label("VariableRangeChecker") == "VRC"
    assert abbrev_label("BitwiseLookup") == "BL"
    assert abbrev_label("PcLookup") == "PL"
    assert abbrev_label("Memory") == "Mem"


def _rows(tmp_path, lo=None, hi=None):
    d = resolve.group_dir("keccak", tmp_path)
    labels = load_bus_map(resolve.base_dump_path(d, "111"))
    return build_sweep(resolve.index_block(d, "111"), labels, lo, hi)


def test_build_sweep_markers_memory_and_sym(tmp_path):
    _make_block(tmp_path)
    rows = _rows(tmp_path)
    assert [r.nnn for r in rows] == [0, 1, 2]
    assert rows[0].fmt == "circuit" and rows[1].fmt == "constraints"
    # circuit step: Memory mult symbolic; constraints steps: concrete
    assert rows[0].sym_busses == ["Memory"]
    assert rows[1].sym_busses == []
    # Memory bus count (id 1): 1 in circuit, 2 in the constraints dumps
    assert rows[0].n_memory == 1
    assert rows[1].n_memory == 2


def test_build_sweep_range_clamp(tmp_path):
    _make_block(tmp_path)
    assert [r.nnn for r in _rows(tmp_path, lo=1)] == [1, 2]
    assert [r.nnn for r in _rows(tmp_path, hi=1)] == [0, 1]
    assert [r.nnn for r in _rows(tmp_path, lo=1, hi=1)] == [1]


def test_render_sweep_json(tmp_path):
    _make_block(tmp_path)
    out = json.loads(render_sweep(_rows(tmp_path), "keccak", "111", JSON))
    assert out["group"] == "keccak" and out["block"] == "111"
    assert len(out["steps"]) == 3
    step0 = out["steps"][0]
    for key in ("nnn", "pass", "format", "n_constraints", "n_bus_interactions",
                "n_memory", "n_derived_columns", "max_degree",
                "distinct_columns", "sym_busses"):
        assert key in step0
    assert step0["sym_busses"] == ["Memory"]  # full label in JSON


def test_render_sweep_plain(tmp_path):
    _make_block(tmp_path)
    text = render_sweep(_rows(tmp_path), "keccak", "111", PLAIN)
    assert "M=machine/circuit C=constraints" in text
    lines = text.splitlines()
    assert lines[2].startswith("000 unopt") and " M " in lines[2]
    assert "Mem" in lines[2]  # abbreviated sym label
    assert lines[3].lstrip().startswith("001 solver")
