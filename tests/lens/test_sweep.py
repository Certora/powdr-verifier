"""Sweep builder, label abbreviation, and sweep rendering."""
import json

from src.lens import resolve
from src.lens.loader import load_bus_map
from src.lens.normalize import normalize_constants
from src.lens.render import (
    JSON, PLAIN, render_subs, render_sweep, render_sweep_all,
)
from src.lens.sweep import abbrev_label, build_sweep, build_sweep_all


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


def _rows(tmp_path, lo=None, hi=None, with_diff=False):
    d = resolve.group_dir("keccak", tmp_path)
    labels = load_bus_map(resolve.base_dump_path(d, "111"))
    return build_sweep(resolve.index_block(d, "111"), labels, lo, hi,
                       with_diff=with_diff)


def _m_bi(ptr):
    """A Memory bus interaction at (as=1, ptr) with one data limb + timestamp."""
    return {"id": 1, "mult": 1, "args": [1, ptr, f"d{ptr}@1", "ts@2"]}


def test_build_sweep_delta_off_by_default(tmp_path):
    _make_block(tmp_path)
    assert all(r.delta is None for r in _rows(tmp_path))  # not computed


def test_build_sweep_delta_vs_prev(tmp_path):
    _make_block(tmp_path)
    rows = _rows(tmp_path, with_diff=True)
    assert rows[0].delta is None            # first row: no prev
    assert rows[1].delta == "xrep"          # 001 (C) vs 000 (M): not comparable
    # 002 (C) vs 001 (C): identical -> all-zero (cons, mem, bus) triples
    assert rows[2].delta == ((0, 0, 0), (0, 0, 0), (0, 0, 0))


def test_build_sweep_delta_memory_separated(tmp_path):
    # two C steps; second drops a memory cell -> dmem removed, dbus untouched
    group = tmp_path / "guest-keccak"
    group.mkdir()
    base = _circuit_dump()
    (group / "apc_candidate_111_000_unopt.json").write_text(json.dumps(base))
    a = {"constraints": [], "derived_columns": [],
         "bus_interactions": [_m_bi(40), _m_bi(44),
                              {"id": 6, "mult": 1, "args": ["x@0", "y@1", 0, 0]}]}
    b = {"constraints": [], "derived_columns": [],
         "bus_interactions": [_m_bi(40),
                              {"id": 6, "mult": 1, "args": ["x@0", "y@1", 0, 0]}]}
    (group / "apc_candidate_111_001_solver.json").write_text(json.dumps(a))
    (group / "apc_candidate_111_002_memory.json").write_text(json.dumps(b))
    rows = _rows(tmp_path, with_diff=True)
    cons, mem, bus = rows[2].delta
    assert mem == (1, 0, 0)   # one memory cell removed
    assert bus == (0, 0, 0)   # bitwise unchanged
    assert cons == (0, 0, 0)


def test_render_sweep_delta_columns_only_with_diff(tmp_path):
    _make_block(tmp_path)
    plain = render_sweep(_rows(tmp_path), "keccak", "111", PLAIN)
    assert "dcons" not in plain  # off by default
    with_d = render_sweep(_rows(tmp_path, with_diff=True), "keccak", "111",
                          PLAIN, with_diff=True)
    assert "dcons" in with_d and "dmem" in with_d and "dbus" in with_d
    assert "—" in with_d         # the cross-representation row


def test_build_sweep_markers_memory_and_sym(tmp_path):
    _make_block(tmp_path)
    rows = _rows(tmp_path)
    assert [r.nnn for r in rows] == [0, 1, 2]
    assert rows[0].fmt == "machine" and rows[1].fmt == "constraints"
    # machine step: Memory mult symbolic; constraints steps: concrete
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
    assert "M=machine C=constraints" in text
    lines = text.splitlines()
    assert lines[2].startswith("000 unopt") and " M " in lines[2]
    assert "Mem" in lines[2]  # abbreviated sym label
    assert lines[3].lstrip().startswith("001 solver")


# --------------------------------------------------------------------------- #
# sweep all
# --------------------------------------------------------------------------- #
def _bus(bid, mult, n):
    return [{"id": bid, "mult": mult, "args": []} for _ in range(n)]


def _write_block(group, bid, cons0, consF, mem0, memF,
                 final_sym_mem=False, final_sym_other=False):
    base = {
        "block": {"blocks": [{"instructions": [[1]]}]},
        "subs": [[0, 1]],
        "bus_map": {"bus_ids": {"1": "Memory", "6": {"Other": "BitwiseLookup"}}},
        "machine": {
            "constraints": [["f@0", "*", ["f@0", "-", 1]]] * cons0,
            "bus_interactions": _bus(1, "sel@9", mem0),  # symbolic in circuit
            "derived_columns": [],
        },
    }
    (group / f"apc_candidate_{bid}_000_unopt.json").write_text(json.dumps(base))
    fbus = _bus(1, 1, memF)
    if final_sym_mem:  # symbolic Memory (id 1) mult
        fbus.append({"id": 1, "mult": ["x@0", "+", "y@1"], "args": []})
    if final_sym_other:  # symbolic non-Memory (BitwiseLookup id 6) mult
        fbus.append({"id": 6, "mult": ["a@0", "+", "b@1"], "args": []})
    final = {
        "constraints": [["f@0", "*", ["f@0", "+", 2013265920]]] * consF,
        "bus_interactions": fbus,
        "derived_columns": [],
    }
    (group / f"apc_candidate_{bid}_001_solver.json").write_text(json.dumps(final))


def _make_multiblock(tmp_path):
    group = tmp_path / "guest-keccak"
    group.mkdir()
    # 111: cons0=5, final has a non-Memory symbolic bus (othSym only)
    # 222: cons0=3, final has a symbolic Memory bus (memSym only)
    _write_block(group, "111", cons0=5, consF=1, mem0=4, memF=2,
                 final_sym_other=True)
    _write_block(group, "222", cons0=3, consF=2, mem0=3, memF=3,
                 final_sym_mem=True)
    return tmp_path


def test_list_blocks(tmp_path):
    _make_multiblock(tmp_path)
    d = resolve.group_dir("keccak", tmp_path)
    assert resolve.list_blocks(d) == ["111", "222"]


def _all_rows(tmp_path, sort="cons0"):
    d = resolve.group_dir("keccak", tmp_path)
    labels = load_bus_map(resolve.base_dump_path(d, "111"))
    return build_sweep_all(d, labels, sort)


def test_build_sweep_all_default_sort_and_fields(tmp_path):
    _make_multiblock(tmp_path)
    rows = _all_rows(tmp_path)
    assert [r.block for r in rows] == ["111", "222"]  # cons0 desc: 5,3
    r = rows[0]
    assert (r.cons0, r.consF, r.n_steps) == (5, 1, 2)
    assert (r.mem0, r.memF) == (4, 2)
    assert r.reduction_pct == 80  # 1 - 1/5
    # 111: non-Memory bus symbolic at final, Memory concrete
    assert r.mem_sym_final is False and r.other_sym_final is True
    assert r.bytes0 > 0
    # 222: Memory bus symbolic at final, no other symbolic
    assert rows[1].mem_sym_final is True
    assert rows[1].other_sym_final is False
    assert rows[1].reduction_pct == 33  # 1 - 2/3


def test_build_sweep_all_sort_consF(tmp_path):
    _make_multiblock(tmp_path)
    rows = _all_rows(tmp_path, sort="consF")
    assert [r.block for r in rows] == ["222", "111"]  # consF desc: 2,1


def test_render_sweep_all_json(tmp_path):
    _make_multiblock(tmp_path)
    out = json.loads(render_sweep_all(_all_rows(tmp_path), "keccak", "cons0", JSON))
    assert out["group"] == "keccak" and out["sort"] == "cons0"
    assert len(out["blocks"]) == 2
    for key in ("block", "n_steps", "cons0", "consF", "reduction_pct",
                "mem0", "memF", "max_degree_final", "mem_sym_final",
                "other_sym_final", "kb0", "bytes0"):
        assert key in out["blocks"][0]


def test_render_sweep_all_plain(tmp_path):
    _make_multiblock(tmp_path)
    text = render_sweep_all(_all_rows(tmp_path), "keccak", "cons0", PLAIN)
    assert "2 blocks" in text
    lines = text.splitlines()
    assert lines[2].split()[:4] == ["111", "2", "5", "1"]  # block steps cons0 consF


# --------------------------------------------------------------------------- #
# subs
# --------------------------------------------------------------------------- #
def test_render_subs_signs_constants():
    raw = [["x@0", 2013265920], ["y@1", [[2013265920, "*", "z@2"], "+", 1]]]
    subs = [(v, normalize_constants(d)) for v, d in raw]
    text = render_subs(subs, "keccak", "111", PLAIN)
    assert "x@0 = -1" in text
    assert "y@1 = ((-1 * z@2) + 1)" in text
    out = json.loads(render_subs(subs, "keccak", "111", JSON))
    assert out["substitutions"][0] == {"var": "x@0", "def": -1}
