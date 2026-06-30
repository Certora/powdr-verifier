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


def test_align_stub_exit_2(capsys):
    assert main(["align", "keccak", "1", "2", "3"]) == 2
    assert "not yet implemented" in capsys.readouterr().err
