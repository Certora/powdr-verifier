"""ResultsDB: reading verification time/status from a report DB."""
import sqlite3

import pytest

from src.lens.results import ResultsDB


def _make_db(path):
    con = sqlite3.connect(str(path))
    con.execute(
        """CREATE TABLE verification_steps (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            input1 TEXT, input2 TEXT, size_bytes INTEGER,
            block INTEGER, passname TEXT, running_time REAL,
            result TEXT, status TEXT, command_line TEXT,
            UNIQUE(input1, input2))"""
    )
    rows = [
        # (block, passname, running_time, result, status)
        (2100224, "001_exec_bus", 120.1, "unknown", "timeout"),
        (2100224, "015_remove_trivial", 300.6, "unsat", "success"),
        (2100224, "051", 321.0, "unsat", "success"),          # bare-NNN final
        (222, "001_solver", 5.0, "sat", "wrong"),
    ]
    for i, (block, pn, rt, res, st) in enumerate(rows):
        con.execute(
            "INSERT INTO verification_steps "
            "(input1, input2, block, passname, running_time, result, status) "
            "VALUES (?,?,?,?,?,?,?)",
            (f"a{i}", f"b{i}", block, pn, rt, res, st),
        )
    con.commit()
    con.close()


def test_step_times_keyed_by_nnn(tmp_path):
    db = tmp_path / "report.db"
    _make_db(db)
    rdb = ResultsDB(db)
    try:
        times = rdb.step_times(2100224)
        assert set(times) == {1, 15, 51}          # NNN from passname prefix
        assert times[15].running_time == 300.6
        assert times[15].status == "success" and times[15].solved is True
        assert times[1].status == "timeout" and times[1].solved is False
        assert times[51].running_time == 321.0    # bare-NNN final joins too
        # block accepts str or int
        assert rdb.step_times("2100224").keys() == times.keys()
    finally:
        rdb.close()


def test_block_summaries(tmp_path):
    db = tmp_path / "report.db"
    _make_db(db)
    rdb = ResultsDB(db)
    try:
        summ = rdb.block_summaries()
        assert summ[2100224].n_steps == 3
        assert summ[2100224].n_solved == 2          # two success, one timeout
        assert summ[2100224].total_time == pytest.approx(741.7)
        assert summ[222].n_solved == 0              # 'wrong' is not solved
    finally:
        rdb.close()


def test_missing_db_raises(tmp_path):
    with pytest.raises(FileNotFoundError):
        ResultsDB(tmp_path / "nope.db")
