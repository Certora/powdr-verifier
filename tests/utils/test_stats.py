import json
import time
from pathlib import Path

import pytest

import src.utils.stats as stats_mod
from src.utils.args import parse_args
from src.utils.stats import (
    init_stats_run,
    prepare_stats_dir,
    profile,
    stats_dump,
    stats_enabled,
    stats_tag_from_path,
    verify_run_id,
)


@pytest.fixture(autouse=True)
def _reset_stats_state():
    stats_mod._stats_dir = None
    stats_mod._current_tag = None
    yield
    stats_mod._stats_dir = None
    stats_mod._current_tag = None


@pytest.fixture
def stats_data_dir(tmp_path, monkeypatch):
    monkeypatch.setattr(stats_mod, "DATA_DIR", tmp_path / "data")
    return stats_mod.DATA_DIR


def test_stats_enabled():
    parse_args(["check", "x.smt2"])
    assert not stats_enabled()
    parse_args(["--stats-run-id", "verify-1-001-002", "check", "x.smt2"])
    assert stats_enabled()


def test_verify_run_id():
    before = Path("apc_candidate_2106368_001_exec_bus.json")
    after = Path("apc_candidate_2106368_002_loop_iteration.json")
    assert verify_run_id(before, after) == "verify-2106368-001-002"


@pytest.mark.parametrize(
    ("path", "tag"),
    [
        (Path("verify-foo.completeness.smt2"), "completeness"),
        (Path("verify-foo.soundness.smt2"), "soundness"),
        (Path("verify-foo.soundness.rewrite.smt2"), "soundness"),
        (Path("verify-foo-bar.smt2"), "encode"),
    ],
)
def test_stats_tag_from_path(path, tag):
    assert stats_tag_from_path(path) == tag


def test_stats_dump_noop_when_disabled(stats_data_dir):
    parse_args(["check", "x.smt2"])
    assert stats_dump("demod", {"x": 1}) is None


def test_stats_dump_writes_file(stats_data_dir):
    smt = stats_data_dir / "guest-keccak" / "verify-2106368-001-002.soundness.smt2"
    smt.parent.mkdir(parents=True)
    parse_args([
        "--stats-run-id", "verify-2106368-001-002",
        "simplify", str(smt), "default", str(smt.with_suffix(".rewrite.smt2")),
    ])
    init_stats_run(wipe=True)
    stats_mod.set_stats_tag("soundness")
    path = stats_dump("demod", {"eqmod_asserts_changed": 3})
    assert path is not None
    assert path.name.endswith("-soundness-demod.json")
    payload = json.loads(path.read_text())
    assert payload["eqmod_asserts_changed"] == 3
    assert payload["tag"] == "soundness"
    assert "t_ns" in payload


def test_prepare_stats_dir_wipes(stats_data_dir):
    run_dir = prepare_stats_dir("guest-keccak", "verify-1-001-002", wipe=True)
    stale = run_dir / "stale.json"
    stale.write_text("{}")
    prepare_stats_dir("guest-keccak", "verify-1-001-002", wipe=True)
    assert not stale.exists()


def test_init_stats_run_subprocess_handoff(stats_data_dir):
    smt = stats_data_dir / "guest-keccak" / "verify-2106368-001-002.soundness.smt2"
    smt.parent.mkdir(parents=True)
    parse_args([
        "--stats-run-id", "verify-2106368-001-002",
        "simplify", str(smt), "default", str(smt.with_suffix(".rewrite.smt2")),
    ])
    prepare_stats_dir("guest-keccak", "verify-2106368-001-002", wipe=True)
    init_stats_run(wipe=False)
    stats_mod.set_stats_tag("soundness")
    first = stats_dump("demod", {"n": 1})
    init_stats_run(wipe=False)
    second = stats_dump("bitwise", {"n": 2})
    assert first is not None and second is not None
    assert first.parent == second.parent
    assert len(list(first.parent.glob("*.json"))) == 2


def test_profile(stats_data_dir):
    smt = stats_data_dir / "guest-keccak" / "verify-2106368-001-002.soundness.smt2"
    smt.parent.mkdir(parents=True)
    parse_args([
        "--stats-run-id", "verify-2106368-001-002",
        "simplify", str(smt), "default", str(smt.with_suffix(".rewrite.smt2")),
    ])
    init_stats_run(wipe=True)
    stats_mod.set_stats_tag("soundness")

    @profile
    def work():
        time.sleep(0.001)
        return 42

    assert work() == 42
    files = list((stats_data_dir / "guest-keccak" / "stats" / "verify-2106368-001-002").glob("*profile-work.json"))
    assert len(files) == 1
    payload = json.loads(files[0].read_text())
    assert payload["name"] == "work"
    assert payload["function"].endswith("work")
    assert payload["t_end_ns"] >= payload["t_ns"]


def test_profile_noop_when_disabled():
    @profile
    def work():
        return 7

    assert work() == 7
