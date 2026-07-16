"""Structured memory-bus analysis for plain permutation encoding."""
from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal

from ..utils.args import ARGS
from .membus_align import (
    _fill_identity_map,
    _heuristic_before_to_after,
    _memory_address_spaces,
    _memory_bus_id,
    _memory_interaction_count,
)
from .membus_subprocess import (
    fetch_align_json,
    fetch_extract_json,
    fetch_info_json,
    fetch_solve_json_all,
)
from .membus_types import MembusParsedKey, parse_membus_key

_LOG = logging.getLogger(__name__)

Tri = bool | None


@dataclass(frozen=True)
class Info:
    """Everything the analysis resolves about a single interaction.

    `matches` stays separate: it is a relation (per-interaction match sets),
    not a scalar attribute, so it does not belong in this per-interaction
    record.
    """

    # Worklist-inferred role flags (tri-valued: True / False / None=unknown).
    input: Tri = None
    output: Tri = None
    disabled: Tri = None
    match: Tri = None
    # Classification: present in ONE circuit only (align status=="removed");
    # never set on the after side. The recv<->send pairing among removed legs is
    # recovered from `matches`, not stored (see `internal_pairs_for`).
    removed: bool = False
    # Trusted parsed timestamp: exact for sends, upper bound for recvs (offset
    # from T), or None. Restricts a recv to matching only earlier sends.
    time: TimeInfo | None = None
    # Trusted parsed membus key (base+offset / const), or None — a syntactic
    # reading of the circuit, used to anchor `pointer == base + offset`.
    key: MembusParsedKey | None = None


@dataclass(frozen=True)
class TimeInfo:
    kind: Literal["exact", "upper"]
    offset: int


@dataclass(frozen=True)
class InternalPair:
    """A forced interior recv<->send connection between two interactions that
    exist in only ONE circuit (align status=="removed"), in membus ordinals."""

    recv: int
    send: int
    addr_space: int


@dataclass
class IdFacts:
    kind: str | None = None
    addr_space: int | None = None
    key: MembusParsedKey | None = None
    time: TimeInfo | None = None
    abstract_ts: str | None = None
    mult_const: int | None = None
    solve_io: str | None = None
    solve_forced: bool = False
    interior_partners: set[int] = field(default_factory=set)


@dataclass
class SideState:
    n: int
    facts: list[IdFacts]
    matches: list[set[int]]
    status: list[list[Tri]]
    removed: list[bool] = field(default_factory=list)
    order_edges: list[dict] = field(default_factory=list)


@dataclass
class MembusAnalysis:
    before_path: Path
    after_path: Path
    before_to_after: dict[int, int]
    before_matches: list[list[int]]
    after_matches: list[list[int]]
    before_info: list[Info]
    after_info: list[Info]
    # before->after pairs sourced from genuine status=="kept" align rows,
    # captured BEFORE any identity fill and left empty on the heuristic fallback
    # (no align ran). The interface encoding trusts only these.
    kept_pairs: dict[int, int] = field(default_factory=dict)

    @property
    def n_before(self) -> int:
        return len(self.before_matches)

    @property
    def n_after(self) -> int:
        return len(self.after_matches)

    def matches_for(self, path: Path) -> list[list[int]]:
        path = path.resolve()
        if path == self.before_path.resolve():
            return self.before_matches
        assert path == self.after_path.resolve(), (
            f"path {path} is neither before {self.before_path} nor after {self.after_path}"
        )
        return self.after_matches

    def info_for(self, path: Path) -> list[Info]:
        """Per-interaction `Info` records (role flags, removed bit, parsed
        time/key) for the given side. See `Info` for field semantics."""
        path = path.resolve()
        if path == self.before_path.resolve():
            return self.before_info
        assert path == self.after_path.resolve(), (
            f"path {path} is neither before {self.before_path} nor after {self.after_path}"
        )
        return self.after_info

    def removed_for(self, path: Path) -> frozenset[int]:
        """Ordinals of this side's removed interactions (present in ONE circuit
        only): the union of the forced interior pair legs and the inert rows.
        Empty when no align ran (and always empty on the after side in v1)."""
        return frozenset(i for i, st in enumerate(self.info_for(path)) if st.removed)

    def internal_pairs_for(self, path: Path) -> list[tuple[int, int]]:
        """Forced interior recv<->send pairs among this side's removed
        interactions, recovered from the match analysis as mutual singletons.

        The pairing is not stored: a removed, non-inert interaction is (by the
        ``local_partners`` fed into ``_restrict_partners``) a match-singleton
        with its one partner, so ``matches[i] == {j}`` and ``matches[j] == {i}``.
        Returned unordered (``i < j``) — recv/send roles are erased once the
        worklist resolves both legs to ``match``; the consumer
        (``internal_pair_equalities``) re-derives them from the multiplicities.
        Raises if a removed leg is not a clean mutual singleton (the align-shape
        gate in ``_collect_internal_pairs`` runs at construction, but these feed
        SMT equalities, so a corrupted ``matches`` must never pass silently)."""
        status = self.info_for(path)
        matches = self.matches_for(path)
        pairs: list[tuple[int, int]] = []
        seen: set[int] = set()
        for i, st in enumerate(status):
            if i in seen or not st.removed or st.disabled:
                continue
            cand = [j for j in matches[i] if j != i]
            partner = cand[0] if len(cand) == 1 else None
            if (
                partner is None
                or partner in seen
                or not status[partner].removed
                or status[partner].disabled
                or [x for x in matches[partner] if x != partner] != [i]
            ):
                raise RuntimeError(
                    f"internal pair recovery: removed interaction #{i} is not a "
                    f"forced mutual singleton (match={matches[i]})"
                )
            seen.add(i)
            seen.add(partner)
            pairs.append((i, partner) if i < partner else (partner, i))
        return pairs


def _normalize_dump(data: dict[str, Any]) -> dict[str, Any]:
    if "machine" in data:
        return data
    return {
        "machine": {
            "constraints": data.get("constraints", []),
            "bus_interactions": data.get("bus_interactions", []),
            "derived_columns": data.get("derived_columns", []),
        },
        "bus_map": {"bus_ids": {"1": "Memory"}},
    }


def _parse_addr_space(raw: Any) -> int | None:
    if raw is None or raw == "sym":
        return None
    return int(raw)


def _parse_time(s: str | None) -> TimeInfo | None:
    if not s:
        return None
    s = s.strip()
    if s.startswith("<=T"):
        rest = s[3:]
        if rest.startswith("+"):
            return TimeInfo("upper", int(rest[1:]))
        if rest.startswith("-"):
            return TimeInfo("upper", -int(rest[1:]))
        return TimeInfo("upper", 0)
    if s.startswith("T"):
        rest = s[1:]
        if rest.startswith("+"):
            return TimeInfo("exact", int(rest[1:]))
        if rest.startswith("-"):
            return TimeInfo("exact", -int(rest[1:]))
        if rest == "":
            return TimeInfo("exact", 0)
    return None


# Transitive closure over timestamp ordering; unordered pairs as sorted 2-tuples.
def _ordered_ts_pairs(order_edges: list[dict]) -> set[tuple[str, str]]:
    nodes = sorted({e["lhs"] for e in order_edges} | {e["rhs"] for e in order_edges})
    if not nodes:
        return set()
    idx = {n: i for i, n in enumerate(nodes)}
    n = len(nodes)
    # Bitset transitive closure: ~1.6s -> ~0.1s per side on 2099828 step 0 membus analysis.
    reach = [0] * n
    for e in order_edges:
        reach[idx[e["lhs"]]] |= 1 << idx[e["rhs"]]
    for k in range(n):
        bit_k = 1 << k
        rk = reach[k]
        if not rk:
            continue
        for i in range(n):
            if reach[i] & bit_k:
                reach[i] |= rk
    return {
        (nodes[i], nodes[j])
        for i in range(n)
        for j in range(i + 1, n)
        if (reach[i] >> j) & 1 or (reach[j] >> i) & 1
    }


def _eval_const_expr(m: Any) -> int | None:
    """Evaluate a powdr multiplicity expression to a constant, if it is one.

    Inlining/substitution can present a constant multiplicity as an
    expression tree rather than a literal — e.g. the recv multiplicity ``-1``
    as ``["-", 1]`` instead of the field literal ``p-1``. Recognising only
    bare ints here would classify such a multiplicity as unknown and defeat
    the input/output/disabled forcing (isinput would stay symbolic, and the
    read byte range would be lost). Fold the common arithmetic node forms.
    """
    if isinstance(m, bool):
        return None
    if isinstance(m, int):
        return m
    if isinstance(m, dict) and "Constant" in m:
        return int(m["Constant"])
    if isinstance(m, list) and m and isinstance(m[0], str):
        op, operands = m[0], [_eval_const_expr(a) for a in m[1:]]
        if any(o is None for o in operands):
            return None
        if op == "-":
            return -operands[0] if len(operands) == 1 else operands[0] - operands[1]
        if op == "+":
            return sum(operands)
        if op == "*":
            r = 1
            for o in operands:
                r *= o
            return r
    return None


def _json_mult_const(data: dict, mem_id: int) -> list[int | None]:
    out: list[int | None] = []
    for bi in data["machine"]["bus_interactions"]:
        if bi["id"] != mem_id:
            continue
        out.append(_eval_const_expr(bi["mult"]))
    return out


def _same_key(a: IdFacts, b: IdFacts) -> bool:
    if a.key is None or b.key is None:
        return False
    if a.key.kind != b.key.kind:
        return False
    if a.key.kind == "const":
        return a.key.const_value == b.key.const_value
    return a.key.base == b.key.base and a.key.offset == b.key.offset


def _keys_cannot_match(a: IdFacts, b: IdFacts) -> bool:
    if a.addr_space is not None and b.addr_space is not None and a.addr_space != b.addr_space:
        return True
    if a.kind is not None and b.kind is not None:
        if a.kind == b.kind and a.kind in ("send", "recv"):
            return True
    if a.key is not None and b.key is not None:
        if a.key.kind == "const" and b.key.kind == "const":
            if a.key.const_value != b.key.const_value:
                return True
        if a.key.kind == "base_offset" and b.key.kind == "base_offset":
            if a.key.base == b.key.base and a.key.offset != b.key.offset:
                return True
    return False


def _times_cannot_match(a: IdFacts, b: IdFacts) -> bool:
    ta, tb = a.time, b.time
    if ta is None or tb is None:
        return False
    if ta.kind == "exact" and tb.kind == "exact" and ta.offset != tb.offset:
        return True
    if ta.kind == "exact" and tb.kind == "upper" and ta.offset > tb.offset:
        return True
    if tb.kind == "exact" and ta.kind == "upper" and tb.offset > ta.offset:
        return True
    return False


def _set_flag(st: list[Tri], idx: int, val: Tri) -> bool:
    if st[idx] == val:
        return False
    st[idx] = val
    return True


def _make_info(st: list[Tri], removed: bool, fact: IdFacts) -> Info:
    return Info(st[0], st[1], st[2], st[3], removed, fact.time, fact.key)


def _apply_boundary_io(status: list[list[Tri]], i: int, io: str | None) -> None:
    match io:
        case "in":
            _set_flag(status[i], 1, False)
            _set_flag(status[i], 3, False)
        case "out":
            _set_flag(status[i], 0, False)
            _set_flag(status[i], 3, False)


def _apply_forced_io(status: list[list[Tri]], i: int, io: str | None) -> None:
    """Pin I/O status from a forced membus solve row (``io`` is authoritative)."""
    match io:
        case "in":
            _set_flag(status[i], 0, True)
            _set_flag(status[i], 1, False)
            _set_flag(status[i], 2, False)
            _set_flag(status[i], 3, False)
        case "out":
            _set_flag(status[i], 0, False)
            _set_flag(status[i], 1, True)
            _set_flag(status[i], 2, False)
            _set_flag(status[i], 3, False)


def _apply_local_role(
    status: list[list[Tri]],
    i: int,
    f: IdFacts,
    *,
    role: str | None,
    partners: list[int],
    io: str | None,
) -> None:
    if role == "inert":
        _set_flag(status[i], 2, True)
    elif role == "interior":
        f.interior_partners.update(partners)
    io_eff = io
    if not io_eff and role in ("input", "output"):
        io_eff = {"input": "in", "output": "out"}[role]
    if io_eff:
        f.solve_io = io_eff
        _apply_boundary_io(status, i, io_eff)


def _merge_info(f: IdFacts, raw: dict) -> None:
    if raw.get("kind"):
        f.kind = raw["kind"]
    if raw.get("address_space") is not None:
        f.addr_space = _parse_addr_space(raw["address_space"])
    if raw.get("key"):
        f.key = parse_membus_key(raw["key"])
    t = _parse_time(raw.get("time"))
    if t is not None:
        f.time = t


def _merge_extract(f: IdFacts, raw: dict) -> None:
    if raw.get("abstract_ts") is not None:
        f.abstract_ts = raw["abstract_ts"]
    if f.addr_space is None and raw.get("address_space") is not None:
        f.addr_space = _parse_addr_space(raw["address_space"])
    if f.key is None and raw.get("key"):
        f.key = parse_membus_key(raw["key"])


def _merge_solve(f: IdFacts, raw: dict) -> None:
    if raw.get("kind") and not f.kind:
        f.kind = raw["kind"]
    if f.addr_space is None and raw.get("address_space") is not None:
        f.addr_space = _parse_addr_space(raw["address_space"])
    if raw.get("key") and not f.key:
        f.key = parse_membus_key(raw["key"])
    if raw.get("forced") is False:
        return
    if raw.get("forced") is True:
        f.solve_forced = True
    if raw.get("io"):
        f.solve_io = raw["io"]
    vint = raw.get("vtime_int")
    if vint is not None:
        f.time = TimeInfo("exact", int(vint))
    elif raw.get("io") == "in":
        f.time = TimeInfo("upper", 0)
    rf = raw.get("reads_from")
    if rf is not None:
        f.interior_partners.add(int(rf))
    for rb in raw.get("read_by") or []:
        f.interior_partners.add(int(rb))



def _ingest_side(
    data: dict,
    path: Path,
    *,
    solve: dict | None,
    info: dict | None,
    extract: dict | None,
    align_rows: list[dict] | None = None,
) -> SideState:
    mem_id = _memory_bus_id(data)
    assert mem_id is not None
    n = _memory_interaction_count(data)
    facts = [IdFacts() for _ in range(n)]
    mults = _json_mult_const(data, mem_id)
    order_edges: list[dict] = []
    unordered: list[dict] = []

    if info:
        for raw in info.get("interactions") or []:
            o = raw.get("ordinal")
            if o is None or o >= n:
                continue
            _merge_info(facts[o], raw)

    if extract:
        order_edges = list(extract.get("order_edges") or [])
        unordered = list(extract.get("unordered") or [])
        for raw in extract.get("interactions") or []:
            o = raw.get("ordinal")
            if o is None or o >= n:
                continue
            _merge_extract(facts[o], raw)

    if solve:
        for raw in solve.get("interactions") or []:
            o = raw.get("ordinal")
            if o is None or o >= n:
                continue
            _merge_solve(facts[o], raw)

    for o in range(n):
        if o < len(mults):
            facts[o].mult_const = mults[o]

    matches = [set(range(n)) for _ in range(n)]
    status = [[None, None, None, None] for _ in range(n)]
    removed = [False] * n

    if align_rows:
        for raw in align_rows:
            o = raw.get("before_id")
            if o is None or o >= n:
                continue
            if raw.get("status") == "removed":
                removed[o] = True
            if raw.get("kind") and not facts[o].kind:
                facts[o].kind = raw["kind"]
            if raw.get("key") and not facts[o].key:
                facts[o].key = parse_membus_key(raw["key"])
            _apply_local_role(
                status,
                o,
                facts[o],
                role=raw.get("local_role"),
                partners=list(raw.get("local_partners") or []),
                io=raw.get("io"),
            )

    for i in range(n):
        f = facts[i]
        match f.kind:
            case "recv":
                _set_flag(status[i], 1, False)
            case "send":
                _set_flag(status[i], 0, False)
            case "disabled":
                _set_flag(status[i], 2, True)

        mc = f.mult_const
        if mc is not None:
            p = ARGS().field_type.value
            mc = mc % p
            if mc == 0:
                _set_flag(status[i], 2, True)
            else:
                _set_flag(status[i], 2, False)
                if mc == p - 1:
                    _set_flag(status[i], 1, False)
                elif mc == 1:
                    _set_flag(status[i], 0, False)

        if f.solve_io:
            if f.solve_forced:
                _apply_forced_io(status, i, f.solve_io)
            else:
                _apply_boundary_io(status, i, f.solve_io)

    if unordered:
        _LOG.warning(
            "membus analysis: %s has %d unordered abstract timestamp(s)",
            path,
            len(unordered),
        )

    return SideState(
        n=n,
        facts=facts,
        matches=matches,
        status=status,
        removed=removed,
        order_edges=order_edges,
    )


def _rule_out_pairs(state: SideState, ordered_ts: set[tuple[str, str]]) -> None:
    n = state.n
    for i, j in itertools.combinations(range(n), 2):
        a, b = state.facts[i], state.facts[j]
        if _keys_cannot_match(a, b):
            _remove_match(state, i, j)
            continue
        if _times_cannot_match(a, b):
            _remove_match(state, i, j)
            continue
        tai, taj = a.abstract_ts, b.abstract_ts
        if tai and taj and ((tai, taj) if tai < taj else (taj, tai)) in ordered_ts:
            _remove_match(state, i, j)


def _remove_match(state: SideState, i: int, j: int) -> None:
    state.matches[i].discard(j)
    state.matches[j].discard(i)


def _restrict_partners(state: SideState) -> None:
    p = ARGS().field_type.value
    for i, f in enumerate(state.facts):
        if not f.interior_partners:
            continue
        self_ruled_out = f.mult_const is not None and f.mult_const % p != 0
        allowed = set(f.interior_partners)
        if not self_ruled_out and not f.solve_forced:
            allowed.add(i)
        drop = [j for j in state.matches[i] if j not in allowed]
        for j in drop:
            _remove_match(state, i, j)
        if self_ruled_out:
            state.matches[i].discard(i)
            _set_flag(state.status[i], 3, True)


def _enqueue(work: set[tuple[int, str]], i: int, channel: str) -> None:
    work.add((i, channel))


def _apply_exactly_one(st: list[Tri]) -> bool:
    trues = [k for k, v in enumerate(st) if v is True]
    if len(trues) > 1:
        return False
    changed = False
    if len(trues) == 1:
        for k in range(4):
            if k != trues[0] and st[k] is not False:
                st[k] = False
                changed = True
        return changed
    falses = sum(1 for v in st if v is False)
    if falses == 3:
        for k, v in enumerate(st):
            if v is None:
                st[k] = True
                return True
    return False


def _run_worklist(state: SideState) -> None:
    n = state.n
    work: set[tuple[int, str]] = {(i, ch) for i in range(n) for ch in ("targets", "status")}

    while work:
        i, channel = work.pop()

        if channel == "status":
            st = state.status[i]
            if _apply_exactly_one(st):
                _enqueue(work, i, "status")
                _enqueue(work, i, "targets")

            if st[3] is True:
                if i in state.matches[i]:
                    state.matches[i].discard(i)
                    _enqueue(work, i, "targets")
            elif st[3] is False:
                if state.matches[i] != {i}:
                    old = state.matches[i] - {i}
                    state.matches[i] = {i}
                    for j in old:
                        _enqueue(work, j, "targets")

            if st[0] is True:
                for k in range(n):
                    if k != i and _same_key(state.facts[i], state.facts[k]):
                        if _set_flag(state.status[k], 0, False):
                            _enqueue(work, k, "status")
            if st[1] is True:
                for k in range(n):
                    if k != i and _same_key(state.facts[i], state.facts[k]):
                        if _set_flag(state.status[k], 1, False):
                            _enqueue(work, k, "status")

        if channel == "targets":
            mset = state.matches[i]
            if i not in mset and state.status[i][3] is not True:
                if _set_flag(state.status[i], 3, True):
                    _enqueue(work, i, "status")

            if mset == {i}:
                if _set_flag(state.status[i], 3, False):
                    _enqueue(work, i, "status")
                for k in range(n):
                    if k != i and i in state.matches[k]:
                        state.matches[k].discard(i)
                        _enqueue(work, k, "targets")

            elif len(mset) == 1:
                j = next(iter(mset))
                if j != i and state.matches[j] == {i}:
                    if _set_flag(state.status[i], 3, True):
                        _enqueue(work, i, "status")
                    if _set_flag(state.status[j], 3, True):
                        _enqueue(work, j, "status")
                    for k in range(n):
                        if k not in (i, j):
                            if i in state.matches[k]:
                                state.matches[k].discard(i)
                                _enqueue(work, k, "targets")
                            if j in state.matches[k]:
                                state.matches[k].discard(j)
                                _enqueue(work, k, "targets")

            elif len(mset) == 0:
                _LOG.warning("membus analysis: interaction %d has empty match set", i)


def _resolve_status(st: list[Tri]) -> None:
    while True:
        changed = False
        if _apply_exactly_one(st):
            changed = True
        if st[3] is True:
            for k in range(3):
                if st[k] is not False:
                    st[k] = False
                    changed = True
        elif st[3] is False:
            roles = st[0:3]
            if not any(v is True for v in roles):
                unknown = [k for k, v in enumerate(roles) if v is None]
                if sum(v is False for v in roles) == 2 and len(unknown) == 1:
                    st[unknown[0]] = True
                    changed = True
        if not changed:
            break


def _finalize_side(state: SideState) -> tuple[list[list[int]], list[Info]]:
    for i in range(state.n):
        _resolve_status(state.status[i])
    matches = [sorted(s) for s in state.matches]
    # One `Info` per interaction: resolved role flags + removed bit + parsed
    # time/key. `removed` is index-guarded so a hand-built state that omits it
    # (shorter list) finalizes as not-removed instead of truncating the output.
    info = [
        _make_info(st, i < len(state.removed) and bool(state.removed[i]), f)
        for i, (st, f) in enumerate(zip(state.status, state.facts))
    ]
    return matches, info


def _analyze_side(
    data: dict,
    path: Path,
    *,
    solve: dict | None,
    info: dict | None,
    extract: dict | None,
    align_rows: list[dict] | None = None,
) -> SideState:
    state = _ingest_side(
        data,
        path,
        solve=solve,
        info=info,
        extract=extract,
        align_rows=align_rows,
    )
    ordered_ts = _ordered_ts_pairs(state.order_edges)
    _rule_out_pairs(state, ordered_ts)
    _restrict_partners(state)
    _run_worklist(state)
    return state


def _exchange_across_alignment(
    before: SideState, after: SideState, before_to_after: dict[int, int]
) -> None:
    """Transfer resolved role/match knowledge across a genuine 1:1 kept
    alignment, then re-run each side's worklist once (a single pass suffices --
    see the note at the transfer below).

    For a kept pair ``(i_b, i_a)`` the two interactions are the SAME memory
    operation up to ``is_valid`` gating, so under ``is_valid==1`` they share
    roles and matches. Filling an unresolved status flag / narrowing a match set
    on one side from the other is a sound *instantiation* of that side's
    quantified permutation variables: instantiating a forall-bound variable can
    only fail to close a proof, never cause a false PASS, and the transferred
    value is exactly the ``is_valid==1`` witness (which is also the determined
    value on the ``is_valid``-asserting soundness side). The symbolic-mult side
    (typically ``after``, whose multiplicities are ``+-is_valid``) thus inherits
    the constant side's resolution and its permutation booleans stop being free
    -- eliminating the residual ``forall`` that made completeness not-qf.

    No explicit ``is_valid`` guard is needed: the alignment already carries the
    ``is_valid==1`` assumption (see ``keyed_io_relation``'s aligned-pair I/O
    ``Iff``s), and forall-instantiation is unconditionally sound regardless."""
    pairs = {
        b: a
        for b, a in before_to_after.items()
        if b < before.n and a < after.n
    }
    if not pairs:
        return
    inverse = {a: b for b, a in pairs.items()}

    def xfer_status(src: SideState, dst: SideState, src2dst: dict[int, int]) -> bool:
        changed = False
        for si, di in src2dst.items():
            for k in range(4):
                if src.status[si][k] is not None and dst.status[di][k] is None:
                    dst.status[di][k] = src.status[si][k]
                    changed = True
        return changed

    def xfer_matches(src: SideState, dst: SideState, src2dst: dict[int, int]) -> bool:
        changed = False
        for si, di in src2dst.items():
            # image of src's candidate partners in dst's index space
            image = {src2dst[j] for j in src.matches[si] if j in src2dst}
            # only narrow when the resolved partner is still reachable, so we
            # never empty di's own match set on a (rare) misaligned pair
            if not (image & dst.matches[di]):
                continue
            for k in [x for x in dst.matches[di] if x not in image]:
                # don't strand the partner `k` either: on a misaligned pair k's
                # only candidate can be di, and `_remove_match` would leave k
                # with an empty match set (which crashes downstream recovery).
                # Skip such a removal -- an over-matched di is harmless (at worst
                # a residual unpinned var); an empty match set is not.
                if dst.matches[k] == {di}:
                    continue
                _remove_match(dst, di, k)  # keeps matches symmetric
                changed = True
        return changed

    # A single pass suffices: `before` is fully resolved by its constant
    # multiplicities, so the transfer is one-directional (before -> after). One
    # pass fills every aligned `after` slot, the worklist propagates it, and a
    # second pass would move nothing new -- `before` is unchanged and after's
    # newly-resolved vars map only back to already-resolved `before`
    # interactions. (Verified: `_040` blocks need exactly one round, interface
    # zero.) A missed transfer would only leave a var unpinned (residual
    # not-qf), never be unsound, so dropping the fixpoint loop is safe.
    changed = xfer_status(before, after, pairs)
    changed |= xfer_status(after, before, inverse)
    changed |= xfer_matches(before, after, pairs)
    changed |= xfer_matches(after, before, inverse)
    if changed:
        _run_worklist(before)
        _run_worklist(after)


def _collect_internal_pairs(
    rows: list[dict[str, Any]], addr_space: int
) -> tuple[list[InternalPair], set[int]]:
    """Extract the forced interior recv<->send pairs among ``status=="removed"``
    align rows, plus the inert (disabled) removed ordinals.

    align already certifies every non-inert removed row is one leg of a forced
    interior pair wholly inside the removed set (it aborts otherwise); this
    re-verifies that shape cheaply and raises on anything else — the pairs
    become recv==send circuit equalities downstream, so a malformed row must
    never be silently skipped.
    """
    by_id = {row["before_id"]: row for row in rows}
    removed = [row for row in rows if row.get("status") == "removed"]
    pairs: list[InternalPair] = []
    inert: set[int] = set()
    claimed_sends: set[int] = set()
    for row in removed:
        bid = row["before_id"]
        kind = row.get("kind")
        if kind == "disabled" or row.get("local_role") == "inert":
            inert.add(bid)
            continue
        if kind == "send":
            continue  # claimed via its recv; verified below
        if kind != "recv":
            raise RuntimeError(
                f"membus internal pairs: removed interaction #{bid} has "
                f"unexpected kind {kind!r}"
            )
        partners = row.get("local_partners") or []
        if row.get("local_role") != "interior" or len(partners) != 1:
            raise RuntimeError(
                f"membus internal pairs: removed recv #{bid} is not a forced "
                f"interior connection (role={row.get('local_role')!r}, "
                f"partners={partners})"
            )
        send = by_id.get(partners[0])
        if (
            send is None
            or send.get("status") != "removed"
            or send.get("kind") != "send"
            or send.get("local_role") != "interior"
            or bid not in (send.get("local_partners") or [])
        ):
            raise RuntimeError(
                f"membus internal pairs: removed recv #{bid} claims send "
                f"#{partners[0]}, which is not a matching removed interior send"
            )
        if partners[0] in claimed_sends:
            raise RuntimeError(
                f"membus internal pairs: removed send #{partners[0]} claimed "
                f"by more than one recv"
            )
        claimed_sends.add(partners[0])
        pairs.append(InternalPair(recv=bid, send=partners[0], addr_space=addr_space))
    unclaimed = {
        row["before_id"]
        for row in removed
        if row.get("kind") == "send" and row["before_id"] not in claimed_sends
    }
    if unclaimed:
        raise RuntimeError(
            f"membus internal pairs: removed send(s) {sorted(unclaimed)} not "
            f"claimed by any removed recv"
        )
    return pairs, inert


def run_membus_analysis(
    before: dict[str, Any],
    after: dict[str, Any],
    before_path: Path,
    after_path: Path,
    *,
    after_assume_is_valid: bool = False,
) -> MembusAnalysis:
    before = _normalize_dump(before)
    after = _normalize_dump(after)
    before_to_after: dict[int, int] = {}
    before_align_rows: list[dict] = []
    align_ran = False
    present = _memory_address_spaces(before)

    # Align every constant address space present (native AS3 blocks exist in
    # guest-keccak); fall back to the register/memory pair when the set is
    # unknown (symbolic address space).
    for addr_space in sorted(present) if present is not None else (1, 2):
        al = fetch_align_json(before_path, after_path, addr_space=addr_space)
        if al is None:
            continue
        align_ran = True
        rows = al.get("interactions") or []
        before_align_rows.extend(rows)
        for raw in rows:
            aid = raw.get("after_id")
            bid = raw.get("before_id")
            if aid is not None and bid is not None and raw.get("status") == "kept":
                before_to_after[bid] = aid
        # Validation gate only: raises on any malformed removed-interaction shape
        # (unclaimed send, non-mutual partner, non-interior removed row). The
        # `removed` classification is stamped per-interaction in `_ingest_side`
        # and the pairing is recovered downstream from `matches`; we keep this
        # trusted align-side check because those pairs become SMT equalities.
        pairs, inert = _collect_internal_pairs(rows, addr_space)
        if pairs or inert:
            _LOG.info(
                "membus align as=%d: %d internal recv<->send pair(s), %d inert removed",
                addr_space,
                len(pairs),
                len(inert),
            )

    # Snapshot the genuine kept map (align "kept" rows only) before the fallback
    # and identity fill mutate/replace before_to_after; empty when no align ran.
    # The interface encoding trusts only this.
    kept_pairs = dict(before_to_after)

    if not align_ran:
        before_to_after = _heuristic_before_to_after(before, after)

    n_before = _memory_interaction_count(before)
    n_after = _memory_interaction_count(after)
    _fill_identity_map(before_to_after, n_before, n_after)

    before_info_json = fetch_info_json(before_path)
    after_info_json = fetch_info_json(after_path)
    before_extract = fetch_extract_json(before_path)
    after_extract = fetch_extract_json(after_path)
    before_solve = fetch_solve_json_all(before_path, present=present)
    after_solve = fetch_solve_json_all(
        after_path, present=present, assume_is_valid=after_assume_is_valid
    )

    before_state = _analyze_side(
        before,
        before_path,
        solve=before_solve,
        info=before_info_json,
        extract=before_extract,
        align_rows=before_align_rows,
    )
    after_state = _analyze_side(
        after,
        after_path,
        solve=after_solve,
        info=after_info_json,
        extract=after_extract,
    )
    # With a genuine kept alignment, share resolved roles/matches across the
    # aligned pairs so the symbolic-mult (is_valid) side inherits the constant
    # side's pins -- otherwise its permutation booleans stay free and make the
    # completeness VC not-qf. Only the genuine kept map (never the heuristic
    # fill) is trusted here.
    if align_ran and kept_pairs:
        _exchange_across_alignment(before_state, after_state, kept_pairs)
    before_matches, before_info = _finalize_side(before_state)
    after_matches, after_info = _finalize_side(after_state)

    _LOG.info(
        "membus analysis: n_before=%d n_after=%d aligned_pairs=%d",
        n_before,
        n_after,
        len(before_to_after),
    )

    return MembusAnalysis(
        before_path=before_path,
        after_path=after_path,
        before_to_after=before_to_after,
        before_matches=before_matches,
        after_matches=after_matches,
        before_info=before_info,
        after_info=after_info,
        kept_pairs=kept_pairs,
    )
