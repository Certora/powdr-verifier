"""Join optimizer dumps to benchmark report DBs.

The report DBs (``report-<group>-<ts>.db`` in the powdr-verifier-benchmarks
repo) record how long each equivalence check took and whether it was solved.
Schema is defined by ``src/report/database.py``:

- ``verification_steps`` — one row per *pass transition* (input1 = step N-1,
  input2 = step N). Keyed for us by ``(block INT, passname)`` where
  ``passname`` is ``NNN_pass`` (e.g. ``015_remove_trivial``), matching the
  lens step label. ``status='success'`` means the check was solved (result
  matched expected); other statuses are timeout / memout / wrong / error.
- ``substeps`` — a nested per-check tree (not read here).

Join to lens dumps by ``(int(block), leading-NNN of passname)``.
"""
from __future__ import annotations

import re
import sqlite3
from dataclasses import dataclass
from pathlib import Path

_NNN = re.compile(r"^(\d+)")


@dataclass(frozen=True)
class StepResult:
    """One block-step's verification outcome from the report DB."""

    running_time: float | None
    status: str | None
    result: str | None

    @property
    def solved(self) -> bool:
        return self.status == "success"


@dataclass(frozen=True)
class BlockResult:
    """One block's aggregate outcome across all its recorded steps."""

    n_steps: int      # rows in the DB (transitions) — one fewer than dump count
    n_solved: int
    total_time: float


class ResultsDB:
    """Read-only accessor over a benchmark report DB."""

    def __init__(self, path: Path | str):
        self.path = Path(path)
        if not self.path.is_file():
            raise FileNotFoundError(f"results DB not found: {self.path}")
        self._con = sqlite3.connect(f"file:{self.path}?mode=ro", uri=True)

    def close(self) -> None:
        self._con.close()

    def step_times(self, block: str | int) -> dict[int, StepResult]:
        """Map NNN -> StepResult for one block (NNN = leading digits of passname)."""
        out: dict[int, StepResult] = {}
        rows = self._con.execute(
            "SELECT passname, running_time, status, result "
            "FROM verification_steps WHERE block=?",
            (int(block),),
        )
        for passname, rt, status, result in rows:
            m = _NNN.match(passname or "")
            if m:
                out[int(m.group(1))] = StepResult(rt, status, result)
        return out

    def block_summaries(self) -> dict[int, BlockResult]:
        """Map int(block) -> BlockResult for every block in the DB."""
        out: dict[int, BlockResult] = {}
        rows = self._con.execute(
            "SELECT block, COUNT(*), "
            "SUM(CASE WHEN status='success' THEN 1 ELSE 0 END), "
            "COALESCE(SUM(running_time), 0) "
            "FROM verification_steps GROUP BY block"
        )
        for block, n, solved, total in rows:
            out[int(block)] = BlockResult(int(n), int(solved or 0), float(total or 0))
        return out
