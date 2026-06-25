"""Build a compact per-step view of one block's optimization trail."""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from .loader import load
from .metrics import DumpStats
from .resolve import StepEntry

_WORD = re.compile(r"[A-Z][a-z0-9]*")


def abbrev_label(label: str) -> str:
    """Compact a bus label for the sym column.

    Multi-word CamelCase -> initials (ExecutionBridge -> EB,
    VariableRangeChecker -> VRC); single word -> first 3 chars (Memory -> Mem).
    """
    words = _WORD.findall(label)
    if len(words) >= 2:
        return "".join(w[0] for w in words)
    return label[:3]


@dataclass
class StepRow:
    """One optimization step's compact stats."""

    nnn: int
    pass_name: str
    fmt: str
    n_constraints: int
    n_bus_interactions: int
    n_memory: int
    n_derived_columns: int
    max_degree: int
    distinct_columns: int
    sym_busses: list[str]

    def as_dict(self) -> dict[str, Any]:
        return {
            "nnn": self.nnn,
            "pass": self.pass_name,
            "format": self.fmt,
            "n_constraints": self.n_constraints,
            "n_bus_interactions": self.n_bus_interactions,
            "n_memory": self.n_memory,
            "n_derived_columns": self.n_derived_columns,
            "max_degree": self.max_degree,
            "distinct_columns": self.distinct_columns,
            "sym_busses": self.sym_busses,
        }


def build_sweep(
    entries: list[StepEntry],
    labels: dict[str, str],
    lo: int | None = None,
    hi: int | None = None,
) -> list[StepRow]:
    """Compute a StepRow per entry whose NNN is within ``[lo, hi]``."""
    rows: list[StepRow] = []
    for e in entries:
        if lo is not None and e.nnn < lo:
            continue
        if hi is not None and e.nnn > hi:
            continue
        s = DumpStats.from_data(load(e.path), labels)
        rows.append(StepRow(
            nnn=e.nnn,
            pass_name=e.pass_name,
            fmt=s.fmt,
            n_constraints=s.n_constraints,
            n_bus_interactions=s.n_bus_interactions,
            n_memory=s.memory_count,
            n_derived_columns=s.n_derived_columns,
            max_degree=s.degree.max,
            distinct_columns=s.distinct_columns,
            sym_busses=s.sym_bus_labels(),
        ))
    return rows
