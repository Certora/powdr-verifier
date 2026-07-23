"""CLI dispatch, --file-a override, error/exit codes."""
import json

from src.membus.cli import main


def _write_dump(tmp_path):
    p = tmp_path / "circuit.json"
    p.write_text(json.dumps({
        "bus_interactions": [
            {"id": 1, "mult": 1, "args": [1, 8, 0, 0, 0, 0, "from_state__timestamp_0@1"]},
            {"id": 1, "mult": 2013265920, "args": [1, 8, 0, 0, 0, 0, "p@2"]},
        ],
        "constraints": [],
    }))
    return p


def test_stats_via_file(tmp_path, capsys):
    rc = main(["stats", "--file-a", str(_write_dump(tmp_path)), "-p"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "n_memory\t2" in out


def test_info_json_via_file(tmp_path, capsys):
    rc = main(["info", "--file-a", str(_write_dump(tmp_path)), "--json"])
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert len(data["interactions"]) == 2


def test_resolve_error_exit_2(capsys):
    assert main(["stats", "no-such-group", "000", "000", "-p"]) == 2
    assert "membus:" in capsys.readouterr().err


def _mem(ptr, mult, ts):
    return {"id": 1, "mult": mult, "args": [1, ptr, 0, 0, 0, 0, ts]}


def _align_pair(tmp_path):
    # sends share one base clock (fs0), a later send at fs0+3 — the same
    # from_state_0-relative frame real dumps carry after inlining, so before
    # and after match by timestamp.
    fs0 = "from_state__timestamp_0@1"
    fs1 = [fs0, "+", 3]
    pva, pvb = "aux__base__prev_timestamp_0@7", "aux__base__prev_timestamp_1@8"
    before = {
        "bus_interactions": [
            _mem(8, 1, fs0), _mem(8, -1, pva), _mem(8, 1, fs1), _mem(8, -1, pvb)],
        "constraints": [
            [[fs0, "+", [-1, "*", pva]], "+", -1],
            [[fs1, "+", [-1, "*", pvb]], "+", -1]],
    }
    after = {"bus_interactions": [_mem(8, -1, pva), _mem(8, 1, fs1)], "constraints": []}
    b = tmp_path / "before.json"; b.write_text(json.dumps(before))
    a = tmp_path / "after.json"; a.write_text(json.dumps(after))
    return b, a


def test_align_via_files(tmp_path, capsys):
    b, a = _align_pair(tmp_path)
    rc = main(["align", "--file-a", str(b), "--file-b", str(a), "--as", "1", "--json"])
    assert rc == 0
    d = json.loads(capsys.readouterr().out)
    assert d["counts"]["kept"] == 2 and d["counts"]["removed"] == 2 and d["unique"] is True


def test_align_needs_two_circuits_exit_2(tmp_path, capsys):
    b, _ = _align_pair(tmp_path)
    assert main(["align", "--file-a", str(b), "-p"]) == 2
    assert "two circuits" in capsys.readouterr().err
