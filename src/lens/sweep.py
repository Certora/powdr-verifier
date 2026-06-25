"""Build a compact per-step view of one block's optimization trail."""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from pathlib import Path

from .loader import load
from .metrics import DumpStats
from .resolve import StepEntry, index_block, list_blocks

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


@dataclass
class BlockRow:
    """One block's initial-vs-final summary across its whole trail."""

    block: str
    n_steps: int
    cons0: int
    consF: int
    reduction_pct: int | None
    mem0: int
    memF: int
    max_degree_final: int
    sym_final: bool
    bytes0: int

    @property
    def kb0(self) -> float:
        return round(self.bytes0 / 1024, 1)

    def as_dict(self) -> dict[str, Any]:
        return {
            "block": self.block,
            "n_steps": self.n_steps,
            "cons0": self.cons0,
            "consF": self.consF,
            "reduction_pct": self.reduction_pct,
            "mem0": self.mem0,
            "memF": self.memF,
            "max_degree_final": self.max_degree_final,
            "sym_final": self.sym_final,
            "kb0": self.kb0,
            "bytes0": self.bytes0,
        }


_SORT_KEYS = {
    "cons0": lambda r: r.cons0,
    "consF": lambda r: r.consF,
    "steps": lambda r: r.n_steps,
    "mem0": lambda r: r.mem0,
    "memF": lambda r: r.memF,
    "size": lambda r: r.bytes0,
    "red": lambda r: r.reduction_pct if r.reduction_pct is not None else -1,
}


def build_sweep_all(
    directory: Path,
    labels: dict[str, str],
    sort_key: str = "cons0",
) -> list[BlockRow]:
    """One BlockRow per block in ``directory``, sorted by ``sort_key`` desc.

    Parses only each block's first and last step (not the whole trail).
    """
    rows: list[BlockRow] = []
    for bid in list_blocks(directory):
        entries = index_block(directory, bid)
        s0 = DumpStats.from_data(load(entries[0].path), labels)
        sf = DumpStats.from_data(load(entries[-1].path), labels)
        red = None if s0.n_constraints == 0 else round(
            100 * (1 - sf.n_constraints / s0.n_constraints))
        rows.append(BlockRow(
            block=bid,
            n_steps=len(entries),
            cons0=s0.n_constraints,
            consF=sf.n_constraints,
            reduction_pct=red,
            mem0=s0.memory_count,
            memF=sf.memory_count,
            max_degree_final=sf.degree.max,
            sym_final=bool(sf.sym_bus_labels()),
            bytes0=entries[0].path.stat().st_size,
        ))
    keyfn = _SORT_KEYS.get(sort_key, _SORT_KEYS["cons0"])
    rows.sort(key=keyfn, reverse=True)
    return rows


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
