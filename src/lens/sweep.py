"""Build a compact per-step view of one block's optimization trail."""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from pathlib import Path

from .diff import counts_from_keys, dump_keys
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
    mem_key_sym: int = 0   # Memory interactions with a symbolic (addr,ptr) key
    # diff vs the previous step: None (first), "xrep" (cross-representation,
    # not comparable), or (cons, mem, bus) each a (rem, add, chg) triple.
    delta: Any = None

    @staticmethod
    def _rac(t) -> dict:
        return {"removed": t[0], "added": t[1], "changed": t[2]}

    def _delta_dict(self) -> Any:
        if self.delta is None:
            return None
        if self.delta == "xrep":
            return {"cross_representation": True}
        cons, mem, bus = self.delta
        return {
            "constraints": self._rac(cons),
            "memory": self._rac(mem),
            "bus": self._rac(bus),
        }

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
            "mem_key_sym": self.mem_key_sym,
            "diff": self._delta_dict(),
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
    mem_sym_final: bool
    other_sym_final: bool
    mem_key_sym_final: bool
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
            "mem_sym_final": self.mem_sym_final,
            "other_sym_final": self.other_sym_final,
            "mem_key_sym_final": self.mem_key_sym_final,
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
        sym_labels = sf.sym_bus_labels()
        rows.append(BlockRow(
            block=bid,
            n_steps=len(entries),
            cons0=s0.n_constraints,
            consF=sf.n_constraints,
            reduction_pct=red,
            mem0=s0.memory_count,
            memF=sf.memory_count,
            max_degree_final=sf.degree.max,
            mem_sym_final="Memory" in sym_labels,
            other_sym_final=any(lbl != "Memory" for lbl in sym_labels),
            mem_key_sym_final=sf.memory_key_sym > 0,
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
    with_diff: bool = False,
) -> list[StepRow]:
    """Compute a StepRow per entry whose NNN is within ``[lo, hi]``.

    When ``with_diff`` is set, each emitted row carries a diff summary vs the
    previous emitted row (same representation only, else ``"xrep"``). Diffing is
    off by default because it is expensive on large blocks.
    """
    rows: list[StepRow] = []
    prev: tuple | None = None   # (keys, fmt) of the previous emitted step
    for e in entries:
        if lo is not None and e.nnn < lo:
            continue
        if hi is not None and e.nnn > hi:
            continue
        data = load(e.path)
        s = DumpStats.from_data(data, labels)
        delta = None
        if with_diff:
            keys = dump_keys(data)              # canonicalize this step once
            delta = _step_delta(prev, keys, s.fmt)
            prev = (keys, s.fmt)
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
            mem_key_sym=s.memory_key_sym,
            delta=delta,
        ))
    return rows


def _step_delta(prev, keys, fmt):
    """Counts-only diff of precomputed `keys` vs `prev` (keys, fmt).

    Returns None (no prev), "xrep" (cross-representation), or (cons, mem, bus).
    """
    if prev is None:
        return None
    pkeys, pfmt = prev
    if pfmt != fmt or fmt not in ("machine", "constraints"):
        return "xrep"
    c = counts_from_keys(pkeys, keys)
    return (c["cons"], c["mem"], c["bus"])
