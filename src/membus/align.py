"""Align the memory bus of two circuits (before / after a removal pass), AS1/AS2.

Given a `before` and an `after` where after removed some memory-bus interactions,
account for **every** before interaction, in robust ids (membus ordinals):

- **cross-match (a)**: kept interactions map to their equivalent in after
  (`before_id -> after_id`), matched **purely by timestamp** — `(eff_kind,
  canonical timestamp)`. The match is a *guess*: a wrong match costs only
  completeness downstream (an unprovable VC), never soundness, and passes do
  not rewrite the timestamp of an interaction they keep (they DO rewrite
  pointer expressions — re-association, limb substitution — which is why the
  pointer is not part of the match key).
- **local connection (b/c)**: from `solve(before)` — a recv to the local send it
  reads, a send to the local recv that reads it. Independent of (a): a kept recv
  can also read a local send. On symbolic-key spaces (AS2) only claims `solve`
  marked FORCED — entailed under every aliasing resolution — are committed; a
  removal justified by anything less aborts.

`mult == 0` interactions are inert: removed and matched to nothing.

This is a HIGH-CONFIDENCE tool. It commits to a local connection only if
`solve(before)` is **globally unique**, and it ABORTS (raises ``ValueError`` ->
CLI exit 2) rather than emit a mapping it cannot justify: after must be a subset
of before, the removed set must self-balance, matches must be unambiguous, and
every in-scope multiplicity must resolve to send/recv/disabled.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.lens.diff import canon_constraint

from . import keys, order, solve
from .busmodel import MemRow, require_explicit_address_spaces
from .rules import Analysis


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


def _kind(an: Analysis, row: MemRow) -> str:
    """Effective kind (send/recv/disabled) from the shared EffKind facts."""
    k = an.kinds.get(row.ordinal)
    return k.kind if k is not None else "sym"


def _ts_key(an: Analysis, row: MemRow) -> Any:
    """(kind, canonical timestamp) — the match identity. Purely timestamp-based:
    the pointer is NOT part of the key (passes rewrite pointer expressions of
    kept interactions; they don't rewrite timestamps)."""
    return (_kind(an, row), repr(canon_constraint(row.ts)))


def _vtime_key(an: Analysis, row: MemRow, soff: dict) -> Any:
    """('send', VIRTUAL TIME) for a send whose ts resolves, else None.

    Only sends need this: `inlining` rewrites send timestamps (`from_state_K` ->
    `from_state_0 + offset`) but leaves recvs (a `prev_timestamp` free witness)
    alone. Virtual time (from `send_offsets`) is representation-independent, so
    an inlined send still matches its pre-inline self."""
    if _kind(an, row) != "send":
        return None
    col = order.ts_col(row.ts)
    vt = soff.get(col) if col else None
    return None if vt is None else ("send", vt + order.intra_offset(row.ts))


def _index(an: Analysis, rows: list[MemRow], keyfn, side: str) -> dict[Any, int]:
    idx: dict[Any, int] = {}
    for row in rows:
        k = keyfn(an, row)
        if k is None:
            continue
        if k in idx:
            raise ValueError(f"align: ambiguous {side} interactions #{idx[k]} and "
                             f"#{row.ordinal} share the same (kind, timestamp)")
        idx[k] = row.ordinal
    return idx


def _cross_match(an_b: Analysis, B: list[MemRow], an_a: Analysis, A: list[MemRow]):
    """Match before<->after interactions. Returns (kept: before_ord->after_ord,
    removed: set[before_ord], added: list[after_ord]).

    Tier 1: exact canonical timestamp (handles same-representation removals and
    recvs). Tier 2: virtual time for the still-unmatched SENDS (handles
    `inlining`, which rewrites send timestamps)."""
    _index(an_b, B, _ts_key, "before")               # before keys must be unique too
    a_canon = _index(an_a, A, _ts_key, "after")
    matched_a: set[int] = set()
    kept: dict[int, int] = {}
    b_left: list[MemRow] = []
    for row in B:
        aid = a_canon.get(_ts_key(an_b, row))
        if aid is not None:
            kept[row.ordinal] = aid
            matched_a.add(aid)
        else:
            b_left.append(row)

    soff_b, soff_a = order.send_offsets(an_b), order.send_offsets(an_a)
    a_left = [r for r in A if r.ordinal not in matched_a]
    a_vt = _index(an_a, a_left, lambda an, r: _vtime_key(an, r, soff_a), "after")
    removed: set[int] = set()
    for row in b_left:
        aid = a_vt.get(_vtime_key(an_b, row, soff_b))
        if aid is not None:
            if aid in matched_a:
                raise ValueError(
                    f"align: two before interactions match after interaction #{aid} "
                    f"(ambiguous virtual-time match)")
            kept[row.ordinal] = aid
            matched_a.add(aid)
        else:
            removed.add(row.ordinal)

    added = [r.ordinal for r in A if r.ordinal not in matched_a]
    return kept, removed, added


def compute(before: Any, after: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Alignment:
    """Align before/after memory busses for ``addr_space``. Raises ``ValueError``
    (CLI -> exit 2) on any condition it cannot justify."""
    if addr_space not in (1, 2):
        raise ValueError(f"align: unsupported address space {addr_space} (supported: 1, 2)")

    an_b = Analysis(before, mem_id, assume_is_valid)
    an_a = Analysis(after, mem_id, assume_is_valid)

    # solved form (both sides): explicit address spaces (a symbolic AS could BE
    # addr_space and would be silently dropped by the `== addr_space` filter) AND
    # resolved multiplicities (a symbolic or otherwise unsupported mult can't be
    # committed to a send/recv/disabled). Refuse rather than guess.
    require_explicit_address_spaces(an_b.mem, "align (before)")
    require_explicit_address_spaces(an_a.mem, "align (after)")
    for label, an in (("align (before)", an_b), ("align (after)", an_a)):
        for row in an.mem:
            if row.addr_space == addr_space and an.kinds.get(row.ordinal) is None:
                raise ValueError(
                    f"{label}: interaction #{row.ordinal} has an unresolved multiplicity "
                    f"{row.mult!r} -- requires solved form (send/recv/disabled)")

    B = [r for r in an_b.mem if r.addr_space == addr_space]
    A = [r for r in an_a.mem if r.addr_space == addr_space]
    if not B:
        raise ValueError(f"align: before has no memory interactions (id={mem_id}, as={addr_space})")

    kept, removed, added = _cross_match(an_b, B, an_a, A)
    if added:
        raise ValueError(
            f"align: after has {len(added)} interaction(s) not present in before "
            f"(e.g. #{added[0]}) -- not a pure removal")

    non_inert_removed = {o for o in removed if an_b.kinds[o].kind != "disabled"}
    if addr_space != 1 and not non_inert_removed:
        # A pure-kept mapping is a justified bijection on its own (mult == 0
        # removals are inert and need none) — no solve required.
        return _align_without_solve(an_b, B, A, kept, removed, mem_id, addr_space)

    # local connections for the removed set. AS1 (constant keys) requires the
    # globally unique graph solution; symbolic-key spaces commit per-row claims
    # that solve marked FORCED (entailed under every aliasing resolution).
    sol = solve.compute(before, mem_id, addr_space, assume_is_valid)   # ValueError -> abort
    if addr_space == 1 and not sol.unique:
        raise ValueError(
            "align: solve(before) is not globally unique; cannot commit to local connections")
    row_of = {r.ordinal: r for r in sol.rows}

    # self-balance: every removed non-inert interaction pairs with a removed
    # partner, via a claim that is forced (unique/entailed), never a guess
    for o in removed:
        r = row_of[o]
        if r.kind == "disabled":
            continue                                          # inert: matched to nothing
        if not r.forced:
            raise ValueError(
                f"align: removed interaction #{o} has no forced local connection "
                f"(its matching varies with aliasing) -- cannot justify the removal")
        if r.kind == "recv":
            if r.io == "in":
                raise ValueError(f"align: removed a boundary input recv #{o} (reads entry)")
            if r.reads_from not in removed:
                raise ValueError(
                    f"align: removed recv #{o} reads local send #{r.reads_from}, which is "
                    f"kept -- removed set does not self-balance")
        elif r.kind == "send":
            if r.io == "out":
                raise ValueError(f"align: removed a boundary output send #{o} (escapes)")
            if not r.read_by or any(x not in removed for x in r.read_by):
                raise ValueError(
                    f"align: removed send #{o} is read by a kept recv -- removed set does "
                    f"not self-balance")

    rows: list[AlignRow] = []
    n_local_pairs = n_inert = 0
    for mem_row in B:
        r = row_of[mem_row.ordinal]
        status = "kept" if mem_row.ordinal in kept else "removed"
        after_id = kept.get(mem_row.ordinal)
        if r.kind == "disabled":
            role, partners = "inert", []
            if status == "removed":
                n_inert += 1
        elif not r.forced:
            role, partners = "", []                # a guess is reported by solve, not here
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
        rows.append(AlignRow(mem_row.ordinal, r.kind, r.key, status, after_id,
                             role, partners, r.io, r.vtime))

    return Alignment(mem_id, addr_space, True, sol.assumed_is_valid,
                     len(B), len(A), len(kept), len(removed), n_local_pairs, n_inert, rows)


def _align_without_solve(an_b: Analysis, B: list[MemRow], A: list[MemRow],
                         kept, removed, mem_id, addr_space) -> Alignment:
    """Alignment rows for a pure-kept non-AS1 pair: cross-match only.

    Reached only when nothing non-inert was removed (the caller routes actual
    removals through `solve`), so the mapping is a justified bijection with no
    local connections. Keys are recovered for display only."""
    from .facts import Assumption

    rows: list[AlignRow] = []
    n_inert = 0
    used_is_valid = False
    for row in B:
        kf = an_b.kinds[row.ordinal]                      # resolved (checked above)
        kind = kf.kind
        if Assumption.ACTIVE_SELECTOR in kf.assumptions:
            used_is_valid = True
        status = "kept" if row.ordinal in kept else "removed"
        if status == "removed" and kind != "disabled":
            raise ValueError(
                f"align: interaction #{row.ordinal} was removed -- removal in address "
                f"space {addr_space} requires solve, which does not support it yet")
        if kind == "disabled" and status == "removed":
            n_inert += 1
        role = "inert" if kind == "disabled" else ""
        rows.append(AlignRow(row.ordinal, kind, str(keys.recover_key(an_b, row)), status,
                             kept.get(row.ordinal), role, [], "", ""))
    return Alignment(mem_id, addr_space, True, used_is_valid, len(B), len(A),
                     len(kept), len(removed), 0, n_inert, rows)
