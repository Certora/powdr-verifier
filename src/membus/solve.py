"""Solve an address space's memory-bus constraints: recover the read↔write
matching per memory cell, and classify each interaction as an **input**, an
**output**, or interior **data flow**.

Graph solver for AS1, where every active memory interaction has a constant
key. All inputs come from certified facts (:class:`~.rules.Analysis`):
EffKind for directions, Gap facts (via ``send_offsets``) for send times,
RecvUpper facts for recv bounds — a recv with several bounds uses their
**intersection** (minimum threshold), so a solution respects every extracted
constraint, not just the first one found.

Per-cell matching rules:

- Per constant key (cell) the sends are totally ordered (positions ``1..k``).
- Each recv's feasible sends are the **prefix** ``{1 .. cutoff-1}``: its
  ``prev_ts`` witness equals the matched send's time and is bounded by its
  RecvUpper thresholds.
- The one recv with ``cutoff == 1`` (empty prefix) reads the **entry** value
  ⟹ **input**; the lone send no recv reads ⟹ **output**.
- A complete recv→send mapping (a bijection respecting the prefixes, with the
  single input recv reading entry) is **a solution**. It is **unique** iff
  exactly one boundary recv exists and the sorted interior cutoffs are
  ``2,3,…,k``.

Raises ``ValueError`` (CLI → exit 2) whenever a precondition cannot be
justified; it never downgrades to a warning.
"""
from __future__ import annotations

import bisect
import collections
from dataclasses import dataclass, field
from typing import Any

from . import keys, order
from .busmodel import MemRow, find_duplicates, require_explicit_address_spaces
from .facts import Assumption
from .rules import Analysis


def _t(n: int) -> str:
    """Virtual time relative to ts_entry (T), as ``T+n`` / ``T-n`` / ``T``."""
    return "T" if n == 0 else (f"T+{n}" if n > 0 else f"T{n}")


@dataclass
class SolveRow:
    """One memory interaction in the solved address space."""
    ordinal: int           # membus ordinal (robust id, stable across AS filters)
    kind: str              # send / recv / disabled
    addr_space: str
    key: str               # str(Key), e.g. "const 8"
    io: str                # "in" | "out" | ""
    vtime: str             # virtual time rel. ts_entry
    flow: str              # data-flow annotation ("← #s" / "← entry" / "→ #r,…" / "→ exit")
    key_value: int | None
    vtime_int: int | None  # send: write time; recv: matched send's time; None if input
    reads_from: int | None
    read_by: list[int]

    def as_dict(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal, "kind": self.kind, "address_space": self.addr_space,
            "key": self.key, "key_value": self.key_value, "io": self.io,
            "vtime": self.vtime, "vtime_int": self.vtime_int,
            "reads_from": self.reads_from, "read_by": self.read_by, "flow": self.flow,
        }


@dataclass
class CellResult:
    """The solved matching for one memory cell (constant key)."""
    key: int
    n_send: int
    n_recv: int
    unique: bool
    note: str                          # "" if solved cleanly, else why not
    edges: list[tuple[int, int]] = field(default_factory=list)   # (recv_ord, send_ord)
    input_recv: int | None = None
    output_send: int | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "key": self.key, "n_send": self.n_send, "n_recv": self.n_recv,
            "unique": self.unique, "note": self.note,
            "edges": [{"recv": r, "send": s} for r, s in self.edges],
            "input_recv": self.input_recv, "output_send": self.output_send,
        }


@dataclass
class Solution:
    mem_id: int
    addr_space: int
    ts_entry: int
    ts_exit: int | None
    rows: list[SolveRow]
    cells: list[CellResult]
    unique: bool             # every cell solved cleanly and uniquely
    n_inputs: int
    n_outputs: int
    assumed_is_valid: bool   # multiplicities were resolved by assuming is_valid==1
    assumptions: frozenset[Assumption] = frozenset()   # named premises actually used

    def as_dict(self) -> dict[str, Any]:
        return {
            "mem_id": self.mem_id, "address_space": self.addr_space,
            "ts_entry": self.ts_entry, "ts_exit": self.ts_exit,
            "unique": self.unique, "n_inputs": self.n_inputs, "n_outputs": self.n_outputs,
            "assumed_is_valid": self.assumed_is_valid,
            "assumptions": sorted(a.name for a in self.assumptions),
            "cells": [c.as_dict() for c in self.cells],
            "interactions": [r.as_dict() for r in self.rows],
        }


def _classified(an: Analysis, rows: list[MemRow]) -> tuple[list[MemRow], set[int]]:
    """Split rows into (active send/recv, disabled ordinals); raise on a row
    whose multiplicity does not resolve."""
    active: list[MemRow] = []
    disabled: set[int] = set()
    for row in rows:
        k = an.kinds.get(row.ordinal)
        if k is None:
            raise ValueError(
                f"solve: interaction #{row.ordinal} has unsupported multiplicity "
                f"{row.mult!r} (not send / recv / disabled)")
        if k.kind == "disabled":
            disabled.add(row.ordinal)
        else:
            active.append(row)
    return active, disabled


def _recv_threshold(an: Analysis, soff: dict, pv: str) -> int | None:
    """The intersection (minimum) of all RecvUpper thresholds on ``pv``,
    resolved against the send-offset table. None if no bound resolves."""
    best: int | None = None
    for f in an.recv_uppers.get(pv, []):
        base = soff.get(f.fs)
        if base is None:
            continue
        t = base + f.const
        if best is None or t < best:
            best = t
    return best


def compute(data: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Solution:
    """Solve the memory bus of one circuit for ``addr_space``.

    ``assume_is_valid`` (default True): the final exported APC gates every
    interaction by the openvm activation selector (``mult = ±is_valid``);
    assuming ``is_valid == 1`` resolves those to ordinary send/recv."""
    if addr_space != 1:
        raise ValueError(f"solve: only address space 1 is supported in v1 (got {addr_space})")
    an = Analysis(data, mem_id, assume_is_valid)
    if "constraints" not in an.machine or "bus_interactions" not in an.machine:
        raise ValueError("solve: dump has no constraints / bus_interactions to solve")
    require_explicit_address_spaces(an.mem, "solve")

    scope = [r for r in an.mem if r.addr_space == addr_space]
    if not scope:
        raise ValueError(f"solve: no memory interactions (id={mem_id}, as={addr_space})")

    active, disabled = _classified(an, scope)
    if not active:
        raise ValueError(f"solve: no active memory interactions (id={mem_id}, as={addr_space})")

    dups = find_duplicates(active)
    if dups:
        raise ValueError(
            f"solve: {len(dups)} duplicated memory interaction(s) -- a sound memory bus "
            f"has none; the matching would be ill-defined. First: {dups[0][1]}x {dups[0][0]}")

    key_of: dict[int, int | None] = {}
    for row in scope:
        k = keys.recover_key(an, row)
        if row.ordinal in disabled:
            key_of[row.ordinal] = k.value if isinstance(k, keys.Const) else None
            continue
        if not isinstance(k, keys.Const):
            raise ValueError(
                f"solve: AS {addr_space} has non-constant memkeys (e.g. {k}); only "
                f"constant-key address spaces are supported (graph fast path)")
        key_of[row.ordinal] = k.value

    soff = order.send_offsets(an)
    if not soff or all(v is None for v in soff.values()):
        raise ValueError(
            "solve: timestamps are not all offsets from a fixed base "
            "(send clocks not in one conflict-free gap component)")
    ts_entry = 0
    max_send_vtime: int | None = None

    used: set[Assumption] = set()
    for row in active:
        used |= an.kinds[row.ordinal].all_assumptions()

    by_key: dict[int, list[MemRow]] = collections.defaultdict(list)
    for row in active:
        by_key[key_of[row.ordinal]].append(row)

    meta: dict[int, dict[str, Any]] = {}
    cells: list[CellResult] = []
    n_inputs = n_outputs = 0
    all_unique = True

    for keyval, grp in sorted(by_key.items()):
        sends: list[tuple[int, int]] = []        # (vtime, ordinal)
        recvs: list[tuple[int, int]] = []        # (threshold, ordinal): prev_ts <= threshold
        for row in grp:
            kind = an.kinds[row.ordinal].kind
            tscol = order.ts_col(row.ts)
            if kind == "send":
                if tscol is None:
                    raise ValueError(
                        f"solve: send #{row.ordinal} has no single-column timestamp slot")
                base = soff.get(tscol)
                if base is None:
                    raise ValueError(
                        f"solve: send #{row.ordinal} timestamp is unresolved (no fixed base)")
                vt = base + order.intra_offset(row.ts)
                sends.append((vt, row.ordinal))
                if max_send_vtime is None or vt > max_send_vtime:
                    max_send_vtime = vt
            else:  # recv
                threshold = _recv_threshold(an, soff, tscol) if tscol else None
                if threshold is None:
                    raise ValueError(
                        f"solve: recv #{row.ordinal} is not bounded "
                        f"(no justified LessThan fact)")
                recvs.append((threshold, row.ordinal))
                for f in an.recv_uppers.get(tscol, []):
                    used.update(f.all_assumptions())

        if len({vt for vt, _ in sends}) != len(sends):
            raise ValueError(
                f"solve: cell {keyval} has two writes at the same virtual time -- "
                f"the write order is not determined")

        k = len(sends)
        if k != len(recvs):
            cells.append(CellResult(keyval, k, len(recvs), False, "unbalanced"))
            all_unique = False
            for o in [s[1] for s in sends] + [r[1] for r in recvs]:
                meta[o] = {"note": "unbalanced"}
            continue

        sends.sort()
        send_vtimes = [vt for vt, _ in sends]                    # ascending, positions 1..k
        send_at_pos = {i: (ordn, vt) for i, (vt, ordn) in enumerate(sends, start=1)}

        # feasible sends for a recv = the PREFIX with vtime <= threshold
        recv_cutoff: dict[int, int] = {}
        for threshold, ordn in recvs:
            recv_cutoff[ordn] = 1 + bisect.bisect_right(send_vtimes, threshold)

        boundary = [o for o, c in recv_cutoff.items() if c == 1]
        interior_cutoffs = sorted(c for c in recv_cutoff.values() if c >= 2)
        unique = (len(boundary) == 1 and len(interior_cutoffs) == k - 1
                  and all(c == i + 2 for i, c in enumerate(interior_cutoffs)))

        if len(boundary) != 1:
            cells.append(CellResult(keyval, k, len(recvs), False, "no-single-input"))
            all_unique = False
            for o in [s[1] for s in sends] + [r[1] for r in recvs]:
                meta[o] = {"note": "no-single-input"}
            continue

        # complete matching: ascending cutoff, take the latest still-free send
        avail = set(range(1, k + 1))
        cell_edges: list[tuple[int, int]] = []
        read_by: dict[int, list[int]] = collections.defaultdict(list)
        feasible = True
        for _c, ordn in sorted((c, o) for o, c in recv_cutoff.items() if c >= 2):
            choices = [p for p in avail if p < _c]
            if not choices:
                feasible = False
                break
            p = max(choices)
            avail.discard(p)
            sord, svt = send_at_pos[p]
            cell_edges.append((ordn, sord))
            read_by[sord].append(ordn)
            meta[ordn] = {"io": "", "vtime_int": svt, "reads_from": sord}
        if not feasible:
            cells.append(CellResult(keyval, k, len(recvs), False, "infeasible"))
            all_unique = False
            for o in [s[1] for s in sends] + [r[1] for r in recvs]:
                meta.setdefault(o, {"note": "infeasible"})
            continue

        input_recv = boundary[0]
        meta[input_recv] = {"io": "in", "vtime_int": None, "reads_from": None}
        output_pos = max(avail) if avail else None         # the lone unread send escapes
        output_send = send_at_pos[output_pos][0] if output_pos is not None else None
        for pos, (sord, svt) in send_at_pos.items():
            m = {"vtime_int": svt, "read_by": read_by.get(sord, [])}
            m["io"] = "out" if sord == output_send else ""
            meta[sord] = m
        n_inputs += 1
        n_outputs += 1 if output_send is not None else 0
        all_unique = all_unique and unique
        cells.append(CellResult(keyval, k, len(recvs), unique, "", cell_edges,
                                input_recv, output_send))

    for g in an.gaps:
        used |= g.all_assumptions()
    assumed_iv = any((k := an.kinds.get(r.ordinal)) is not None
                     and Assumption.ACTIVE_SELECTOR in k.assumptions for r in scope)
    rows = _build_rows(an, scope, key_of, meta, str(addr_space), ts_entry, disabled)
    return Solution(mem_id, addr_space, ts_entry, max_send_vtime, rows, cells,
                    all_unique, n_inputs, n_outputs, assumed_iv, frozenset(used))


def _build_rows(an: Analysis, scope: list[MemRow], key_of, meta, asv,
                ts_entry, disabled) -> list[SolveRow]:
    out: list[SolveRow] = []
    for row in sorted(scope, key=lambda r: r.ordinal):
        ordn = row.ordinal
        keyval = key_of[ordn]
        keystr = f"const {keyval}" if keyval is not None else "?"
        if ordn in disabled:
            out.append(SolveRow(ordn, "disabled", asv, keystr, "", ".", "disabled",
                                keyval, None, None, []))
            continue
        kind = an.kinds[ordn].kind
        m = meta.get(ordn, {})
        note = m.get("note")
        io = m.get("io", "")
        vint = m.get("vtime_int")
        reads_from = m.get("reads_from")
        read_by = m.get("read_by", [])
        if note:
            vtime, flow = "?", f"(unsolved: {note})"
        elif kind == "send":
            vtime = _t(vint) if vint is not None else "?"
            flow = "-> exit" if io == "out" else ("-> " + ", ".join(f"#{r}" for r in read_by)
                                                  if read_by else "-> .")
        else:  # recv
            if io == "in":
                vtime, flow = f"<{_t(ts_entry)}", "<- entry"
            else:
                vtime = _t(vint) if vint is not None else "?"
                flow = f"<- #{reads_from}" if reads_from is not None else "<- ?"
        out.append(SolveRow(ordn, kind, asv, keystr, io, vtime, flow,
                            keyval, vint, reads_from, list(read_by)))
    return out
