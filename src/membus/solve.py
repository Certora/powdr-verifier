"""Solve an address space's memory-bus constraints: recover the read↔write
matching per memory cell, and classify each interaction as an **input**, an
**output**, or interior **data flow**.

Graph solver for AS1, where every active memory interaction has a constant
key. It derives send order and recv bounds from timestamp constraints, then
matches recvs to the latest available send in each feasible prefix.

Per-cell matching rules:

- Per constant key (cell) the sends are totally ordered (positions ``1..k``).
- Each recv's feasible sends are the **prefix** ``{1 .. cutoff-1}`` where
  ``cutoff`` is the position of the recv's own-op send (R2: a recv reads a write
  strictly before its own op).
- The one recv with ``cutoff == 1`` (empty prefix) reads the **entry** value
  (``prev_ts < ts_entry``) ⟹ **input**; the lone send no recv reads ⟹ **output**.
- A complete recv→send mapping (a bijection respecting the prefixes, with the
  single input recv reading entry) is **a solution**. We report whether it is
  **unique**: iff exactly one boundary recv and the sorted interior cutoffs are
  ``2,3,…,k``.
"""
from __future__ import annotations

import bisect
import collections
from dataclasses import dataclass, field
from typing import Any

from src.lens.loader import machine_of
from src.lens.metrics import _eval_const, mult_kind
from src.lens.normalize import BABYBEAR_PRIME

from . import keys, order
from .busfmt import find_duplicates, memory_bis


def _is_valid_col(name: str) -> bool:
    """The openvm autoprecompile activation selector ``is_valid`` (global, no
    per-instruction index — distinct from the early-pass ``is_valid_<K>``)."""
    return name.split("@", 1)[0] == "is_valid"


def _kind_assuming_is_valid(mult: Any) -> str | None:
    """Classify a multiplicity under the assumption ``is_valid == 1``.

    The final exported APC gates every interaction by the openvm activation
    selector (``mult = ±is_valid``). With ``is_valid := 1`` this is just a normal
    send/recv. Returns send/recv/disabled when the mult is a linear combination of
    *only* ``is_valid`` columns; otherwise None (a genuinely symbolic mult)."""
    lt = order.linterms(mult)
    if lt is None:
        return None
    coeffs = {k: v for k, v in lt[0].items() if v != 0}
    if not coeffs or any(not _is_valid_col(k) for k in coeffs):
        return None
    val = (lt[1] + sum(coeffs.values())) % BABYBEAR_PRIME      # substitute is_valid := 1
    if val == 1:
        return "send"
    if val == BABYBEAR_PRIME - 1:
        return "recv"
    if val == 0:
        return "disabled"
    return None


def _t(n: int) -> str:
    """Virtual time relative to ts_entry (T), as ``T+n`` / ``T-n`` / ``T``."""
    return "T" if n == 0 else (f"T+{n}" if n > 0 else f"T{n}")


@dataclass
class SolveRow:
    """One memory interaction in the solved address space."""
    ordinal: int           # membus ordinal (robust id, stable across AS filters)
    kind: str              # send / recv
    addr_space: str
    key: str               # str(Key), e.g. "const 8"
    io: str                # "in" | "out" | ""
    vtime: str             # virtual time rel. ts_entry (send: write time; recv: solved prev_ts)
    flow: str              # data-flow annotation ("← #s" / "← entry" / "→ #r,…" / "→ exit")
    key_value: int | None  # the constant address (for JSON / merging)
    vtime_int: int | None  # send: write time; recv: matched send's time; None if input/unsolved
    reads_from: int | None  # recv: ordinal of the send it reads; else None
    read_by: list[int]     # send: ordinals of the recvs that read it

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

    def as_dict(self) -> dict[str, Any]:
        return {
            "mem_id": self.mem_id, "address_space": self.addr_space,
            "ts_entry": self.ts_entry, "ts_exit": self.ts_exit,
            "unique": self.unique, "n_inputs": self.n_inputs, "n_outputs": self.n_outputs,
            "assumed_is_valid": self.assumed_is_valid,
            "cells": [c.as_dict() for c in self.cells],
            "interactions": [r.as_dict() for r in self.rows],
        }


def compute(data: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Solution:
    """Solve the memory bus of one circuit for ``addr_space``. Raises ``ValueError``
    (caught by the CLI → exit 2) when a precondition for the graph solver fails.

    ``assume_is_valid`` (default True): in the final exported APC every interaction
    is gated by the openvm activation selector (``mult = ±is_valid``); assuming
    ``is_valid == 1`` turns those into ordinary send/recv. This only affects that
    final APC — no other step carries the global ``is_valid`` in its multiplicities."""
    if addr_space != 1:
        raise ValueError(f"solve: only address space 1 is supported in v1 (got {addr_space})")
    machine = machine_of(data)
    if "constraints" not in machine or "bus_interactions" not in machine:
        raise ValueError("solve: dump has no constraints / bus_interactions to solve")

    all_bis = memory_bis(data, mem_id)
    rows_idx = [(i, b) for i, b in enumerate(all_bis)
                if keys.address_space_of(b) == addr_space]
    if not rows_idx:
        raise ValueError(f"solve: no memory interactions (id={mem_id}, as={addr_space})")

    # classify: active sends/recvs vs disabled (mult 0 — inert: no timestamp
    # constraint, matches nothing). With assume_is_valid, ±is_valid resolves to
    # send/recv. Other symbolic multiplicities are refused.
    active: list[tuple[int, dict]] = []
    disabled: set[int] = set()
    key_of: dict[int, int | None] = {}
    eff_kind: dict[int, str] = {}
    used_is_valid = False
    for ordn, b in rows_idx:
        kind = mult_kind(b["mult"])
        if kind not in ("send", "recv"):
            ek = _kind_assuming_is_valid(b["mult"]) if assume_is_valid else None
            if ek is not None:
                used_is_valid = True
                kind = ek
            elif (cv := _eval_const(b["mult"])) is not None and cv % BABYBEAR_PRIME == 0:
                kind = "disabled"     # mult == 0 (bare int or column-free expr) -> inert
            else:
                raise ValueError(
                    f"solve: interaction #{ordn} has unsupported multiplicity "
                    f"{b['mult']!r} (not send / recv / disabled)")
        eff_kind[ordn] = kind
        if kind in ("send", "recv"):
            k = keys.recover_key(machine, b)
            if not isinstance(k, keys.Const):
                raise ValueError(
                    f"solve: AS {addr_space} has non-constant memkeys (e.g. {k}); only "
                    f"constant-key address spaces are supported (graph fast path)")
            key_of[ordn] = k.value
            active.append((ordn, b))
        else:  # disabled
            disabled.add(ordn)
            dk = keys.recover_key(machine, b)
            key_of[ordn] = dk.value if isinstance(dk, keys.Const) else None

    if not active:
        raise ValueError(f"solve: no active memory interactions (id={mem_id}, as={addr_space})")

    dups = find_duplicates([b for _, b in active])
    if dups:
        raise ValueError(
            f"solve: {len(dups)} duplicated memory interaction(s) — a sound memory bus "
            f"has none; the matching would be ill-defined. First: {dups[0][1]}× {dups[0][0]}")

    edges, recv_bound, _ = order.deduce(machine)
    chain = order.total_order(machine, edges)
    if not chain:
        raise ValueError("solve: no total send order — ts_entry is not well defined")
    soff = order.send_offsets(machine)
    if any(v is None for v in soff.values()):
        raise ValueError(
            "solve: timestamps are not all offsets from a fixed base (unresolved chain gap)")
    ts_entry = 0
    max_send_vtime: int | None = None     # ts_exit = the last write (post-inline all share one base)

    by_key: dict[int, list[tuple[int, dict]]] = collections.defaultdict(list)
    for ordn, b in active:
        by_key[key_of[ordn]].append((ordn, b))

    # per-ordinal solved metadata, filled in below
    meta: dict[int, dict[str, Any]] = {}
    cells: list[CellResult] = []
    n_inputs = n_outputs = 0
    all_unique = True

    for keyval, grp in sorted(by_key.items()):
        sends: list[tuple[int, int]] = []        # (vtime, ordinal)
        recvs: list[tuple[int, int]] = []        # (threshold, ordinal): prev_ts <= threshold
        for ordn, b in grp:
            kind = eff_kind[ordn]
            tsarg = b["args"][6]
            tscol = order.ts_col(tsarg)
            if kind == "send":
                if tscol is None or not order.is_fs(tscol):
                    raise ValueError(f"solve: send #{ordn} has no from_state timestamp")
                if soff.get(tscol) is None:
                    raise ValueError(f"solve: send #{ordn} timestamp is unresolved (no fixed base)")
                vt = soff[tscol] + order.intra_offset(tsarg)
                sends.append((vt, ordn))
                if max_send_vtime is None or vt > max_send_vtime:
                    max_send_vtime = vt
            elif kind == "recv":
                if tscol is None or tscol not in recv_bound:
                    raise ValueError(f"solve: recv #{ordn} is not bounded (no R2 LessThan gadget)")
                own_fs, _strict, const = recv_bound[tscol]
                if soff.get(own_fs) is None:
                    raise ValueError(f"solve: recv #{ordn} own-op send time is unresolved")
                recvs.append((soff[own_fs] + const, ordn))   # prev_ts <= soff[own_fs] + const
            else:
                raise ValueError(f"solve: interaction #{ordn} is neither send nor recv ({kind})")

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

        # feasible sends for a recv = those with vtime <= threshold (prev_ts == send vtime,
        # bounded by R2). Sorted-by-vtime => a PREFIX; cutoff = 1 + |feasible prefix|.
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

        # complete matching: ascending cutoff, take the latest still-free send in the prefix
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

    rows = _build_rows(rows_idx, key_of, meta, str(addr_space), ts_entry, disabled, eff_kind)
    return Solution(mem_id, addr_space, ts_entry, max_send_vtime, rows, cells,
                    all_unique, n_inputs, n_outputs, used_is_valid)


def _build_rows(rows_idx, key_of, meta, asv, ts_entry, disabled, eff_kind) -> list[SolveRow]:
    out: list[SolveRow] = []
    for ordn, b in sorted(rows_idx):
        keyval = key_of[ordn]
        keystr = f"const {keyval}" if keyval is not None else "?"
        if ordn in disabled:
            out.append(SolveRow(ordn, "disabled", asv, keystr, "", "·", "disabled",
                                keyval, None, None, []))
            continue
        kind = eff_kind[ordn]
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
            flow = "→ exit" if io == "out" else ("→ " + ", ".join(f"#{r}" for r in read_by)
                                                 if read_by else "→ ·")
        else:  # recv
            if io == "in":
                vtime, flow = f"<{_t(ts_entry)}", "← entry"
            else:
                vtime = _t(vint) if vint is not None else "?"
                flow = f"← #{reads_from}" if reads_from is not None else "← ?"
        out.append(SolveRow(ordn, kind, asv, keystr, io, vtime, flow,
                            keyval, vint, reads_from, list(read_by)))
    return out
