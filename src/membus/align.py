"""Align the memory bus of two circuits (before / after a removal pass), AS1/AS2.

Given a `before` and an `after` where after removed some memory-bus interactions,
account for **every** before interaction, in robust ids (membus ordinals):

- **cross-match (a)**: kept interactions map to their equivalent in after
  (`before_id -> after_id`), matched **purely by timestamp** — `(mult_kind,
  canonical timestamp)`. The match is a *guess*: a wrong match costs only
  completeness downstream (an unprovable VC), never soundness, and passes do
  not rewrite the timestamp of an interaction they keep (they DO rewrite
  pointer expressions — re-association, limb substitution — which is why the
  pointer is not part of the match key). `canon(timestamp)` of a bare column is
  its name, so this also gives name-equivalence for column timestamps.
- **local connection (b/c)**: from `solve(before)` — a recv to the local send it
  reads, a send to the local recv that reads it. Independent of (a): a kept recv
  can also read a local send. AS1 only for now: `solve` does not support AS2
  yet, so an AS2 alignment carries no local connections and ABORTS if the pass
  actually removed AS2 interactions (nothing can justify the removal).

`mult == 0` interactions are inert: removed and matched to nothing.

This is a HIGH-CONFIDENCE tool. It commits to a local connection only if
`solve(before)` is **globally unique**, and it ABORTS (raises ``ValueError`` ->
CLI exit 2) rather than emit a mapping it cannot justify: after must be a subset
of before, the removed set must self-balance, and matches must be unambiguous.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.lens.diff import _mem_order
from src.lens.loader import machine_of
from src.lens.metrics import _eval_const, mult_kind
from src.lens.normalize import BABYBEAR_PRIME

from . import keys, order, solve
from .busfmt import memory_bis, require_explicit_address_spaces


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


def _eff_kind(bi: dict, aiv: bool) -> str:
    """Effective send/recv, normalizing the openvm activation selector like `solve`:
    the final APC gates every interaction by `±is_valid`, which `assume_is_valid`
    resolves to a plain send/recv."""
    k = mult_kind(bi["mult"])
    if k not in ("send", "recv") and aiv:
        ek = solve._kind_assuming_is_valid(bi["mult"])
        if ek is not None:
            return ek
    return k


def _ts_key(bi: dict, aiv: bool) -> Any:
    """(kind, canonical timestamp) — the match identity, with the multiplicity
    is_valid-normalized so the final APC matches. Purely timestamp-based: the
    pointer is NOT part of the key (passes rewrite pointer expressions of kept
    interactions; they don't rewrite timestamps)."""
    return (_eff_kind(bi, aiv), _mem_order(bi)[1])


def _vtime_key(bi: dict, soff: dict, aiv: bool) -> Any:
    """('send', VIRTUAL TIME) for a send whose ts resolves, else None.

    Only sends need this: `inlining` rewrites send timestamps (`from_state_K` ->
    `from_state_0 + offset`) but leaves recvs (a `prev_timestamp` free witness)
    alone. Virtual time (from `send_offsets`) is representation-independent, so an
    inlined send still matches its pre-inline self.
    """
    if _eff_kind(bi, aiv) != "send":
        return None
    ts = bi["args"][6]
    col = order.ts_col(ts)
    vt = soff.get(col) if col else None
    return None if vt is None else ("send", vt + order.intra_offset(ts))


def _index(rows_idx, keyfn, side: str) -> dict[Any, int]:
    idx: dict[Any, int] = {}
    for ordn, bi in rows_idx:
        k = keyfn(bi)
        if k is None:
            continue
        if k in idx:
            raise ValueError(f"align: ambiguous {side} interactions #{idx[k]} and #{ordn} "
                             f"share the same (kind, timestamp)")
        idx[k] = ordn
    return idx


def _cross_match(B, soff_b, A, soff_a, aiv):
    """Match before<->after interactions. Returns (kept: before_ord->after_ord,
    removed: set[before_ord], added: list[after_ord]).

    Tier 1: exact canonical timestamp (handles same-representation removals and
    recvs). Tier 2: virtual time for the still-unmatched SENDS (handles `inlining`,
    which rewrites send timestamps). Two tiers keep removals base-independent (they
    match at tier 1) and only use vtime where the representation actually changed.
    """
    _index(B, lambda bi: _ts_key(bi, aiv), "before")     # before keys must be unique too
    a_canon = _index(A, lambda bi: _ts_key(bi, aiv), "after")
    matched_a: set[int] = set()
    kept: dict[int, int] = {}
    b_left = []
    for ordn, bi in B:
        aid = a_canon.get(_ts_key(bi, aiv))
        if aid is not None:
            kept[ordn] = aid
            matched_a.add(aid)
        else:
            b_left.append((ordn, bi))

    a_left = [(o, bi) for o, bi in A if o not in matched_a]
    a_vt = _index(a_left, lambda bi: _vtime_key(bi, soff_a, aiv), "after")
    removed: set[int] = set()
    for ordn, bi in b_left:
        aid = a_vt.get(_vtime_key(bi, soff_b, aiv))
        if aid is not None:
            if aid in matched_a:
                raise ValueError(
                    f"align: two before interactions match after interaction #{aid} "
                    f"(ambiguous virtual-time match)")
            kept[ordn] = aid
            matched_a.add(aid)
        else:
            removed.add(ordn)

    added = [o for o, _ in A if o not in matched_a]
    return kept, removed, added


def compute(before: Any, after: Any, mem_id: int = 1, addr_space: int = 1,
            assume_is_valid: bool = True) -> Alignment:
    """Align before/after memory busses for ``addr_space``. Raises ``ValueError``
    (CLI -> exit 2) on any condition it cannot justify."""
    if addr_space not in (1, 2):
        raise ValueError(f"align: unsupported address space {addr_space} (supported: 1, 2)")

    # solved form (both sides): explicit address spaces (a symbolic AS could BE
    # addr_space and would be silently dropped by the `== addr_space` filter) AND
    # resolved multiplicities (a symbolic mult — pre-solver, `is_valid_K·opcode` —
    # can't be committed to a send/recv). Refuse rather than guess.
    require_explicit_address_spaces(before, mem_id, "align (before)")
    require_explicit_address_spaces(after, mem_id, "align (after)")
    for label, data in (("align (before)", before), ("align (after)", after)):
        for i, b in enumerate(memory_bis(data, mem_id)):
            if keys.address_space_of(b) == addr_space and _eff_kind(b, assume_is_valid) == "sym":
                raise ValueError(f"{label}: interaction #{i} has a symbolic multiplicity "
                                 f"— requires solved form (resolved send/recv)")

    B = [(i, b) for i, b in enumerate(memory_bis(before, mem_id))
         if keys.address_space_of(b) == addr_space]
    A = [(i, b) for i, b in enumerate(memory_bis(after, mem_id))
         if keys.address_space_of(b) == addr_space]
    if not B:
        raise ValueError(f"align: before has no memory interactions (id={mem_id}, as={addr_space})")

    # cross-match: canonical timestamp first, then virtual time for leftover sends
    # (so it survives inlining's send-timestamp rewrite). `send_offsets` gives the
    # vtime on each side — no need to fully solve `after`.
    kept, removed, added = _cross_match(B, order.send_offsets(machine_of(before)),
                                        A, order.send_offsets(machine_of(after)),
                                        assume_is_valid)
    if added:
        raise ValueError(
            f"align: after has {len(added)} interaction(s) not present in before "
            f"(e.g. #{added[0]}) — not a pure removal")

    if addr_space != 1:
        # `solve` is AS1-only, so no local connections. A pure-kept mapping is a
        # justified bijection on its own; an actual removal has nothing to
        # justify it -> abort (mult == 0 removals are inert and need none).
        return _align_without_solve(before, B, A, kept, removed,
                                    mem_id, addr_space, assume_is_valid)

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


def _align_without_solve(before, B, A, kept, removed, mem_id, addr_space,
                         assume_is_valid) -> Alignment:
    """Alignment rows when `solve` is unavailable (AS2): cross-match only.

    Every non-inert before interaction must be kept — a removed send/recv would
    need `solve` to justify its local pairing, so it aborts. Keys are recovered
    for display only (they are not part of the match)."""
    machine = machine_of(before)
    rows: list[AlignRow] = []
    n_inert = 0
    used_is_valid = False
    for ordn, bi in B:
        kind = mult_kind(bi["mult"])
        if kind not in ("send", "recv"):
            ek = solve._kind_assuming_is_valid(bi["mult"]) if assume_is_valid else None
            if ek is not None:
                used_is_valid = True
                kind = ek
            elif (cv := _eval_const(bi["mult"])) is not None and cv % BABYBEAR_PRIME == 0:
                kind = "disabled"
        status = "kept" if ordn in kept else "removed"
        if status == "removed" and kind != "disabled":
            raise ValueError(
                f"align: interaction #{ordn} was removed — removal in address space "
                f"{addr_space} requires solve, which does not support it yet")
        if kind == "disabled" and status == "removed":
            n_inert += 1
        role = "inert" if kind == "disabled" else ""
        rows.append(AlignRow(ordn, kind, str(keys.recover_key(machine, bi)), status,
                             kept.get(ordn), role, [], "", ""))
    return Alignment(mem_id, addr_space, True, used_is_valid, len(B), len(A),
                     len(kept), len(removed), 0, n_inert, rows)
