"""Align the memory bus of two circuits (before / after a removal pass), AS1.

Given a `before` and an `after` where after removed some memory-bus interactions,
account for **every** before interaction, in robust ids (membus ordinals):

- **cross-match (a)**: kept interactions map to their equivalent in after
  (`before_id -> after_id`), matched the way `lens diff` matches membus — by
  `(address_space, pointer)` cell + `(mult_kind, canonical timestamp)`, i.e.
  **semantic, primarily by timestamp, data-free** (pairing is fixed by
  (key, timestamp), not data). `canon(timestamp)` of a bare column is its name,
  so this also gives name-equivalence for column timestamps.
- **local connection (b/c)**: from `solve(before)` — a recv to the local send it
  reads, a send to the local recv that reads it. Independent of (a): a kept recv
  can also read a local send.

`mult == 0` interactions are inert: removed and matched to nothing.

This is a HIGH-CONFIDENCE tool. It commits to a local connection only if
`solve(before)` is **globally unique**, and it ABORTS (raises ``ValueError`` ->
CLI exit 2) rather than emit a mapping it cannot justify: after must be a subset
of before, the removed set must self-balance, and matches must be unambiguous.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.lens.diff import _mem_cell, _mem_order

from . import keys, solve
from .busfmt import memory_bis


@dataclass
class AlignRow:
    before_id: int
    kind: str                    # send / recv / disabled
    key: str                     # str(Key), e.g. "const 8"
    status: str                  # kept / removed
    after_id: int | None         # cross-match (a): equivalent interaction in after
    local_role: str              # input | output | interior | inert
    local_partners: list[int]    # (b/c): local recv->[send], send->[recv]; [] if boundary/inert
    io: str
    vtime: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "before_id": self.before_id, "kind": self.kind, "key": self.key,
            "status": self.status, "after_id": self.after_id,
            "local_role": self.local_role, "local_partners": self.local_partners,
            "io": self.io, "vtime": self.vtime,
        }


@dataclass
class Alignment:
    mem_id: int
    addr_space: int
    unique: bool
    assumed_is_valid: bool
    n_before: int
    n_after: int
    n_kept: int
    n_removed: int
    n_local_pairs: int
    n_inert: int
    rows: list[AlignRow]

    def as_dict(self) -> dict[str, Any]:
        return {
            "mem_id": self.mem_id, "address_space": self.addr_space,
            "unique": self.unique, "assumed_is_valid": self.assumed_is_valid,
            "counts": {
                "before": self.n_before, "after": self.n_after, "kept": self.n_kept,
                "removed": self.n_removed, "local_pairs": self.n_local_pairs,
                "inert": self.n_inert,
            },
            "interactions": [r.as_dict() for r in self.rows],
        }


def _semantic_index(rows_idx: list[tuple[int, dict]], side: str) -> dict[Any, int]:
    """Map each interaction's semantic key -> its membus ordinal, one side.

    Semantic key = (mem cell (address_space, pointer), mult_kind, canonical
    timestamp) — reuses lens's `_mem_cell` / `_mem_order`. Non-unique on a side
    ⟹ ABORT (an ambiguous cell/timestamp collision would make the match a guess).
    """
    idx: dict[Any, int] = {}
    for ordn, bi in rows_idx:
        k = (_mem_cell(bi), _mem_order(bi))
        if k in idx:
            raise ValueError(
                f"align: ambiguous {side} interactions #{idx[k]} and #{ordn} share "
                f"the same (cell, kind, timestamp) — cannot match unambiguously")
        idx[k] = ordn
    return idx


def compute(before: Any, after: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Alignment:
    """Align before/after memory busses for ``addr_space``. Raises ``ValueError``
    (CLI -> exit 2) on any condition it cannot justify."""
    if addr_space != 1:
        raise ValueError(f"align: only address space 1 is supported (got {addr_space})")

    B = [(i, b) for i, b in enumerate(memory_bis(before, mem_id))
         if keys.address_space_of(b) == addr_space]
    A = [(i, b) for i, b in enumerate(memory_bis(after, mem_id))
         if keys.address_space_of(b) == addr_space]
    if not B:
        raise ValueError(f"align: before has no memory interactions (id={mem_id}, as={addr_space})")

    # cross-match by semantic key (kept), leftovers = removed (before) / added (after)
    bkey = _semantic_index(B, "before")
    akey = _semantic_index(A, "after")
    kept = {bkey[k]: akey[k] for k in bkey if k in akey}      # before_ord -> after_ord
    removed = {o for o in bkey.values() if o not in kept}
    added = [akey[k] for k in akey if k not in bkey]
    if added:
        raise ValueError(
            f"align: after has {len(added)} interaction(s) not present in before "
            f"(e.g. #{added[0]}) — not a pure removal")

    # local connections for the removed set — require a globally unique solve
    sol = solve.compute(before, mem_id, addr_space, assume_is_valid)   # ValueError -> abort
    if not sol.unique:
        raise ValueError(
            "align: solve(before) is not globally unique; cannot commit to local connections")
    row = {r.ordinal: r for r in sol.rows}

    # self-balance: every removed non-inert interaction pairs with a removed partner
    for o in removed:
        r = row[o]
        if r.kind == "disabled":
            continue                                          # inert: matched to nothing
        if r.kind == "recv":
            if r.io == "in":
                raise ValueError(f"align: removed a boundary input recv #{o} (reads entry)")
            if r.reads_from not in removed:
                raise ValueError(
                    f"align: removed recv #{o} reads local send #{r.reads_from}, which is "
                    f"kept — removed set does not self-balance")
        elif r.kind == "send":
            if r.io == "out":
                raise ValueError(f"align: removed a boundary output send #{o} (escapes)")
            if not r.read_by or any(x not in removed for x in r.read_by):
                raise ValueError(
                    f"align: removed send #{o} is read by a kept recv — removed set does "
                    f"not self-balance")

    rows: list[AlignRow] = []
    n_local_pairs = n_inert = 0
    for ordn, _bi in B:
        r = row[ordn]
        status = "kept" if ordn in kept else "removed"
        after_id = kept.get(ordn)
        if r.kind == "disabled":
            role, partners = "inert", []
            if status == "removed":
                n_inert += 1
        elif r.kind == "recv":
            if r.io == "in":
                role, partners = "input", []
            else:
                role, partners = "interior", [r.reads_from]
        else:  # send
            if r.io == "out":
                role, partners = "output", []
            else:
                role, partners = "interior", list(r.read_by)
        if status == "removed" and r.kind == "recv" and role == "interior":
            n_local_pairs += 1                                # count each recv<->send pair once
        rows.append(AlignRow(ordn, r.kind, r.key, status, after_id, role, partners,
                             r.io, r.vtime))

    return Alignment(mem_id, addr_space, True, sol.assumed_is_valid,
                     len(B), len(A), len(kept), len(removed), n_local_pairs, n_inert, rows)
