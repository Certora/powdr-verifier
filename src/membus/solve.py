"""Solve an address space's memory-bus constraints: recover the read↔write
matching per memory cell, and classify each interaction as an **input**, an
**output**, or interior **data flow**.

All inputs come from certified facts (:class:`~.rules.Analysis`): EffKind for
directions, Gap facts (via ``send_offsets``) for send times, RecvUpper facts
for recv bounds — a recv with several bounds uses their **intersection**
(minimum threshold), so a solution respects every extracted constraint, not
just the first one found.

**The solution is always computed by the prefix-interval graph algorithm**,
per key group, under the no-aliasing reading (each syntactically distinct
key class treated as a distinct cell — sufficient because any solution will
do, and the no-alias world is always one of the open encoding's models):

- Per cell the sends are totally ordered (positions ``1..k``).
- Each recv's feasible sends are the **prefix** ``{1 .. cutoff-1}``: its
  ``prev_ts`` witness equals the matched send's time and is bounded by its
  RecvUpper thresholds.
- The one recv with ``cutoff == 1`` (empty prefix) reads the **entry** value
  ⟹ **input**; the lone send no recv reads ⟹ **output**.
- A complete recv→send mapping (a bijection respecting the prefixes, with
  the single input recv reading entry) is **a solution**. It is **unique**
  iff exactly one boundary recv exists and the sorted interior cutoffs are
  ``2,3,…,k``.

**Constant keys** (always AS1) commit the alias partition for free: the cell
is `unique` by the prefix criterion, and then every claim is entailed
(`forced`).

**Symbolic keys** (``base + offset``, e.g. AS2) may carry potential aliasing
(a memory-loaded base is not provably disjoint from anything). A cell with
potential aliasing is **never unique** — the solution shown is a guess. Its
individual claims are upgraded to ``forced`` by :mod:`.smtsolve`: a claim is
forced iff blocking it is UNSAT with aliasing left open, i.e. it holds under
EVERY aliasing resolution. Only forced claims may be committed downstream.

Raises ``ValueError`` (CLI → exit 2) whenever a precondition cannot be
justified; it never downgrades to a warning.
"""
from __future__ import annotations

import bisect
import collections
from dataclasses import dataclass, field
from typing import Any

from src.lens.normalize import BABYBEAR_PRIME

from . import keys, order
from .busmodel import MemRow, find_duplicates, require_explicit_address_spaces
from .facts import AffineDef, Assumption
from .linform import linform
from .rules import Analysis

P = BABYBEAR_PRIME


def _t(n: int) -> str:
    """Virtual time relative to ts_entry (T), as ``T+n`` / ``T-n`` / ``T``."""
    return "T" if n == 0 else (f"T+{n}" if n > 0 else f"T{n}")


@dataclass
class SolveRow:
    """One memory interaction in the solved address space."""
    ordinal: int           # membus ordinal (robust id, stable across AS filters)
    kind: str              # send / recv / disabled
    addr_space: str
    key: str               # str(Key), e.g. "const 8" / "rs1_0+40"
    io: str                # "in" | "out" | ""
    vtime: str             # virtual time rel. ts_entry
    flow: str              # data-flow annotation ("← #s" / "← entry" / "→ #r,…" / "→ exit")
    key_value: int | None
    vtime_int: int | None  # send: write time; recv: matched send's time; None if input
    reads_from: int | None
    read_by: list[int]
    forced: bool | None    # claim holds under every aliasing resolution; None if disabled

    def as_dict(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal, "kind": self.kind, "address_space": self.addr_space,
            "key": self.key, "key_value": self.key_value, "io": self.io,
            "vtime": self.vtime, "vtime_int": self.vtime_int,
            "reads_from": self.reads_from, "read_by": self.read_by, "flow": self.flow,
            "forced": self.forced,
        }


@dataclass
class CellResult:
    """The solved matching for one memory cell (one key)."""
    key: int | str
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


# --------------------------------------------------------------------------- #
# the prefix-interval matching core (shared by both key shapes)
# --------------------------------------------------------------------------- #

@dataclass
class _CellMatch:
    """A cell's prefix-interval matching. ``note != ""`` ⟹ no complete
    matching (``edges`` may hold the partial greedy progress)."""
    note: str
    unique: bool
    edges: list[tuple[int, int, int]]       # (recv_ord, send_ord, send_vt), greedy order
    read_by: dict[int, list[int]]
    input_recv: int | None
    output_send: int | None


def _prefix_matching(label: str, sends: list[tuple[int, int]],
                     recvs: list[tuple[int, int]]) -> _CellMatch:
    """Match one cell: ``sends`` = (vtime, ordinal), ``recvs`` = (threshold,
    ordinal). See the module docstring for the rules."""
    if len({vt for vt, _ in sends}) != len(sends):
        raise ValueError(
            f"solve: {label} has two writes at the same virtual time -- "
            f"the write order is not determined")
    k = len(sends)
    if k != len(recvs):
        return _CellMatch("unbalanced", False, [], {}, None, None)

    sends = sorted(sends)
    send_vtimes = [vt for vt, _ in sends]                    # ascending, positions 1..k
    send_at_pos = {i: (ordn, vt) for i, (vt, ordn) in enumerate(sends, start=1)}

    # feasible sends for a recv = the PREFIX with vtime <= threshold
    recv_cutoff = {ordn: 1 + bisect.bisect_right(send_vtimes, threshold)
                   for threshold, ordn in recvs}
    boundary = [o for o, c in recv_cutoff.items() if c == 1]
    interior_cutoffs = sorted(c for c in recv_cutoff.values() if c >= 2)
    unique = (len(boundary) == 1 and len(interior_cutoffs) == k - 1
              and all(c == i + 2 for i, c in enumerate(interior_cutoffs)))

    if len(boundary) != 1:
        return _CellMatch("no-single-input", False, [], {}, None, None)

    # complete matching: ascending cutoff, take the latest still-free send
    avail = set(range(1, k + 1))
    edges: list[tuple[int, int, int]] = []
    read_by: dict[int, list[int]] = collections.defaultdict(list)
    for _c, ordn in sorted((c, o) for o, c in recv_cutoff.items() if c >= 2):
        choices = [p for p in avail if p < _c]
        if not choices:
            return _CellMatch("infeasible", unique, edges, dict(read_by), None, None)
        p = max(choices)
        avail.discard(p)
        sord, svt = send_at_pos[p]
        edges.append((ordn, sord, svt))
        read_by[sord].append(ordn)

    output_pos = max(avail) if avail else None         # the lone unread send escapes
    output_send = send_at_pos[output_pos][0] if output_pos is not None else None
    return _CellMatch("", unique, edges, dict(read_by), boundary[0], output_send)


def compute(data: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Solution:
    """Solve the memory bus of one circuit for ``addr_space``.

    ``assume_is_valid`` (default True): the final exported APC gates every
    interaction by the openvm activation selector (``mult = ±is_valid``);
    assuming ``is_valid == 1`` resolves those to ordinary send/recv."""
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

    key_of: dict[int, keys.Key] = {}
    key_fact: dict[int, AffineDef | None] = {}
    for row in scope:
        key_of[row.ordinal], key_fact[row.ordinal] = keys.recover_key_fact(an, row)

    soff = order.send_offsets(an)
    if not soff or all(v is None for v in soff.values()):
        raise ValueError(
            "solve: timestamps are not all offsets from a fixed base "
            "(send clocks not in one conflict-free gap component)")

    used: set[Assumption] = set()
    for row in active:
        used |= an.kinds[row.ordinal].all_assumptions()

    if all(isinstance(key_of[r.ordinal], keys.Const) for r in active):
        meta, cells, n_in, n_out, max_vt, all_unique = _solve_const(
            an, active, key_of, soff, used)
    else:
        meta, cells, n_in, n_out, max_vt, all_unique = _solve_symbolic(
            an, active, key_of, key_fact, soff, used)

    for g in an.gaps:
        used |= g.all_assumptions()
    assumed_iv = any((k := an.kinds.get(r.ordinal)) is not None
                     and Assumption.ACTIVE_SELECTOR in k.assumptions for r in scope)
    rows = _build_rows(an, scope, key_of, meta, str(addr_space), 0, disabled)
    return Solution(mem_id, addr_space, 0, max_vt, rows, cells,
                    all_unique, n_in, n_out, assumed_iv, frozenset(used))


def _group_times(an: Analysis, grp: list[MemRow], soff: dict, used: set[Assumption],
                 ) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """(sends, recvs) of one cell as (vtime, ordinal) / (threshold, ordinal);
    raises when a send clock or recv bound cannot be justified."""
    sends: list[tuple[int, int]] = []
    recvs: list[tuple[int, int]] = []
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
            sends.append((base + order.intra_offset(row.ts), row.ordinal))
        else:  # recv
            threshold = _recv_threshold(an, soff, tscol) if tscol else None
            if threshold is None:
                raise ValueError(
                    f"solve: recv #{row.ordinal} is not bounded "
                    f"(no justified LessThan fact)")
            recvs.append((threshold, row.ordinal))
            for f in an.recv_uppers.get(tscol, []):
                used.update(f.all_assumptions())
    return sends, recvs


# --------------------------------------------------------------------------- #
# constant keys: the partition is committed for free; unique ⟹ forced
# --------------------------------------------------------------------------- #

def _solve_const(an: Analysis, active: list[MemRow], key_of: dict[int, keys.Key],
                 soff: dict, used: set[Assumption]):
    max_send_vtime: int | None = None

    by_key: dict[int, list[MemRow]] = collections.defaultdict(list)
    for row in active:
        by_key[key_of[row.ordinal].value].append(row)

    meta: dict[int, dict[str, Any]] = {}
    cells: list[CellResult] = []
    n_inputs = n_outputs = 0
    all_unique = True

    for keyval, grp in sorted(by_key.items()):
        sends, recvs = _group_times(an, grp, soff, used)
        for vt, _ in sends:
            if max_send_vtime is None or vt > max_send_vtime:
                max_send_vtime = vt

        match = _prefix_matching(f"cell {keyval}", sends, recvs)
        k = len(sends)
        unique = match.unique

        for ordn, sord, svt in match.edges:
            meta[ordn] = {"io": "", "vtime_int": svt, "reads_from": sord, "forced": unique}
        if match.note:
            cells.append(CellResult(keyval, k, len(recvs), False, match.note))
            all_unique = False
            for o in [s[1] for s in sends] + [r[1] for r in recvs]:
                meta.setdefault(o, {"note": match.note})
            continue

        meta[match.input_recv] = {"io": "in", "vtime_int": None, "reads_from": None,
                                  "forced": unique}
        for svt, sord in sends:
            m = {"vtime_int": svt, "read_by": match.read_by.get(sord, []), "forced": unique}
            m["io"] = "out" if sord == match.output_send else ""
            meta[sord] = m
        n_inputs += 1
        n_outputs += 1 if match.output_send is not None else 0
        all_unique = all_unique and unique
        cells.append(CellResult(keyval, k, len(recvs), unique, "",
                                [(r, s) for r, s, _ in match.edges],
                                match.input_recv, match.output_send))

    return meta, cells, n_inputs, n_outputs, max_send_vtime, all_unique


# --------------------------------------------------------------------------- #
# symbolic keys: graph pre-solution under no-aliasing; claims forced by SMT
# --------------------------------------------------------------------------- #

def _provably_disjoint(k1: keys.Key, k2: keys.Key) -> bool:
    """Distinct keys whose cells are PROVABLY distinct (never alias).

    Constants: distinct canonical residues. Same base, same modulus: distinct
    offsets differ mod m ⟹ the pointers differ (given the [0, p) windows the
    caller checks). Anything else — different bases, a constant against a
    base, mixed moduli — is not provable and stays uncertain."""
    if isinstance(k1, keys.Const) and isinstance(k2, keys.Const):
        return k1.value != k2.value
    if (isinstance(k1, keys.BaseOffset) and isinstance(k2, keys.BaseOffset)
            and k1.base == k2.base and k1.mod == k2.mod):
        return k1.offset != k2.offset
    return False


def _solve_symbolic(an: Analysis, active: list[MemRow], key_of: dict[int, keys.Key],
                    key_fact: dict[int, AffineDef | None], soff: dict,
                    used: set[Assumption]):
    from . import smtsolve

    bad = [r.ordinal for r in active if isinstance(key_of[r.ordinal], keys.Unresolved)]
    if bad:
        raise ValueError(
            f"solve: {len(bad)} interaction(s) have unresolved symbolic memkeys "
            f"(e.g. #{bad[0]} {key_of[bad[0]]}) -- cannot commit an alias partition")

    groups: dict[keys.Key, list[MemRow]] = collections.defaultdict(list)
    for row in active:
        groups[key_of[row.ordinal]].append(row)
    group_keys = sorted(groups, key=str)

    # Grouping premise: one key = one cell. Provable only when every row of the
    # group carries the SAME canonical pointer expression (two expressions that
    # merely share the mod-2^16 label could differ in the high bits).
    for k in group_keys:
        lfs = {linform(row.ptr) for row in groups[k]}
        if len(lfs) != 1:
            raise ValueError(
                f"solve: memkey {k} is claimed by {len(lfs)} different pointer "
                f"expressions -- cannot prove they address the same cell")

    # Window premise: every pointer's integer window must sit inside [0, p), so
    # field (in)equality coincides with integer (in)equality — both for the
    # same-base disjointness proof and for the ℤ encoding of cross-base
    # aliasing. Constants are canonical residues and need no check.
    for k in group_keys:
        if isinstance(k, keys.Const):
            continue
        lf = linform(groups[k][0].ptr)
        win = an._window(list(lf.coeffs), lf.const)
        if win is None or win[0] < 0 or win[1] >= P:
            raise ValueError(
                f"solve: pointer of memkey {k} has no justified [0, p) window -- "
                f"field/integer (in)equality does not transfer")
        for prem in win[2]:
            used |= prem.all_assumptions()
        fact = key_fact[groups[k][0].ordinal]
        if fact is not None:
            used |= fact.all_assumptions()

    # graph pre-solution per group, under the no-aliasing reading
    engine_groups: list[list[smtsolve.EngineRow]] = []
    matches: list[_CellMatch] = []
    claims: dict[int, list[smtsolve.Claim]] = {}
    max_send_vtime: int | None = None
    for gi, k in enumerate(group_keys):
        sends, recvs = _group_times(an, groups[k], soff, used)
        base = None if isinstance(k, keys.Const) else k.base
        offset = (k.value % P) if isinstance(k, keys.Const) else k.offset
        erows = [smtsolve.EngineRow(o, "send", base, offset, vt) for vt, o in sends]
        erows += [smtsolve.EngineRow(o, "recv", base, offset, thr) for thr, o in recvs]
        engine_groups.append(erows)
        for vt, _ in sends:
            if max_send_vtime is None or vt > max_send_vtime:
                max_send_vtime = vt
        match = _prefix_matching(f"cell {k}", sends, recvs)
        matches.append(match)
        if not match.note:
            cl: list[smtsolve.Claim] = [("edge", r, s) for r, s, _ in match.edges]
            cl.append(("input", match.input_recv))
            if match.output_send is not None:
                cl.append(("output", match.output_send))
            claims[gi] = cl

    uncertain: dict[int, set[int]] = collections.defaultdict(set)
    for i in range(len(group_keys)):
        for j in range(i + 1, len(group_keys)):
            if not _provably_disjoint(group_keys[i], group_keys[j]):
                uncertain[i].add(j)
                uncertain[j].add(i)

    meta: dict[int, dict[str, Any]] = {}
    cells: list[CellResult] = []
    n_inputs = n_outputs = 0
    all_unique = True
    for gi, (k, erows, match) in enumerate(zip(group_keys, engine_groups, matches)):
        n_send = sum(1 for r in erows if r.kind == "send")
        n_recv = len(erows) - n_send
        if match.note:
            cells.append(CellResult(str(k), n_send, n_recv, False, match.note))
            all_unique = False
            for r in erows:
                meta[r.ordinal] = {"note": match.note, "forced": False}
            continue

        if not uncertain.get(gi):
            # no potential aliasing: the partition is committed, exactly as
            # for constant keys — prefix-unique ⟹ every claim entailed
            cell_unique = match.unique
            fmap = dict.fromkeys(claims[gi], cell_unique)
        else:
            cell_unique = False                # potential aliasing: never unique
            if smtsolve.cluster_size(engine_groups, uncertain, gi) \
                    > smtsolve.DEFAULT_CLUSTER_CAP:
                fmap = dict.fromkeys(claims[gi], False)
            else:
                fmap = smtsolve.force_group(engine_groups, uncertain, gi, claims)
        all_unique = all_unique and cell_unique

        for r, s, svt in match.edges:
            meta[r] = {"io": "", "vtime_int": svt, "reads_from": s,
                       "forced": fmap[("edge", r, s)]}
        meta[match.input_recv] = {"io": "in", "vtime_int": None, "reads_from": None,
                                  "forced": fmap[("input", match.input_recv)]}
        for row in erows:
            if row.kind != "send":
                continue
            o = row.ordinal
            readers = match.read_by.get(o, [])
            if o == match.output_send:
                f = fmap[("output", o)]
            else:
                f = all(fmap[("edge", r, o)] for r in readers) if readers else False
            meta[o] = {"io": "out" if o == match.output_send else "",
                       "vtime_int": row.time, "read_by": readers, "forced": f}
        n_inputs += 1
        n_outputs += 1 if match.output_send is not None else 0
        cells.append(CellResult(str(k), n_send, n_recv, cell_unique, "",
                                [(r, s) for r, s, _ in match.edges],
                                match.input_recv, match.output_send))

    return meta, cells, n_inputs, n_outputs, max_send_vtime, all_unique


def _build_rows(an: Analysis, scope: list[MemRow], key_of, meta, asv,
                ts_entry, disabled) -> list[SolveRow]:
    out: list[SolveRow] = []
    for row in sorted(scope, key=lambda r: r.ordinal):
        ordn = row.ordinal
        key = key_of.get(ordn)
        keystr = "?" if key is None or isinstance(key, keys.Unresolved) else str(key)
        keyval = key.value if isinstance(key, keys.Const) else None
        if ordn in disabled:
            out.append(SolveRow(ordn, "disabled", asv, keystr, "", ".", "disabled",
                                keyval, None, None, [], None))
            continue
        kind = an.kinds[ordn].kind
        m = meta.get(ordn, {})
        note = m.get("note")
        io = m.get("io", "")
        vint = m.get("vtime_int")
        reads_from = m.get("reads_from")
        read_by = m.get("read_by", [])
        forced = m.get("forced", False)
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
        if not note and not forced:
            flow += "  (unforced)"
        out.append(SolveRow(ordn, kind, asv, keystr, io, vtime, flow,
                            keyval, vint, reads_from, list(read_by), forced))
    return out
