"""Structured memory-bus analysis for plain permutation encoding."""
from __future__ import annotations

import itertools
import logging
from collections import namedtuple
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
Status = namedtuple("Status", ("input", "output", "disabled", "match"))


@dataclass(frozen=True)
class TimeInfo:
    kind: Literal["exact", "upper"]
    offset: int


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
    order_edges: list[dict] = field(default_factory=list)


@dataclass
class MembusAnalysis:
    before_path: Path
    after_path: Path
    before_to_after: dict[int, int]
    before_matches: list[set[int]]
    after_matches: list[set[int]]
    before_status: list[Status]
    after_status: list[Status]

    @property
    def n_before(self) -> int:
        return len(self.before_matches)

    @property
    def n_after(self) -> int:
        return len(self.after_matches)

    def matches_for(self, path: Path) -> list[set[int]]:
        path = path.resolve()
        if path == self.before_path.resolve():
            return self.before_matches
        assert path == self.after_path.resolve(), (
            f"path {path} is neither before {self.before_path} nor after {self.after_path}"
        )
        return self.after_matches

    def status_for(self, path: Path) -> list[Status]:
        path = path.resolve()
        if path == self.before_path.resolve():
            return self.before_status
        assert path == self.after_path.resolve(), (
            f"path {path} is neither before {self.before_path} nor after {self.after_path}"
        )
        return self.after_status


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


def _json_mult_const(data: dict, mem_id: int) -> list[int | None]:
    out: list[int | None] = []
    for bi in data["machine"]["bus_interactions"]:
        if bi["id"] != mem_id:
            continue
        m = bi["mult"]
        if isinstance(m, int):
            out.append(m)
        elif isinstance(m, dict) and "Constant" in m:
            out.append(int(m["Constant"]))
        else:
            out.append(None)
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


def _status_tuple(st: list[Tri]) -> Status:
    return Status(st[0], st[1], st[2], st[3])


def _apply_boundary_io(status: list[list[Tri]], i: int, io: str | None) -> None:
    match io:
        case "in":
            _set_flag(status[i], 1, False)
            _set_flag(status[i], 3, False)
        case "out":
            _set_flag(status[i], 0, False)
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

    if align_rows:
        for raw in align_rows:
            o = raw.get("before_id")
            if o is None or o >= n:
                continue
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


def _finalize_side(state: SideState) -> tuple[list[set[int]], list[Status]]:
    for i in range(state.n):
        _resolve_status(state.status[i])
    matches = [set(s) for s in state.matches]
    status = [_status_tuple(st) for st in state.status]
    return matches, status


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


def run_membus_analysis(
    before: dict[str, Any],
    after: dict[str, Any],
    before_path: Path,
    after_path: Path,
) -> MembusAnalysis:
    before = _normalize_dump(before)
    after = _normalize_dump(after)
    before_to_after: dict[int, int] = {}
    before_align_rows: list[dict] = []
    align_ok = False
    present = _memory_address_spaces(before)

    for addr_space in (1, 2, 3):
        if present is not None and addr_space not in present:
            continue
        al = fetch_align_json(before_path, after_path, addr_space=addr_space)
        if al is None:
            continue
        align_ok = True
        before_align_rows.extend(al.get("interactions") or [])
        for raw in al.get("interactions") or []:
            aid = raw.get("after_id")
            bid = raw.get("before_id")
            if aid is not None and bid is not None and raw.get("status") == "kept":
                before_to_after[bid] = aid
        # TODO: align provides "local" for removed entries

    if not align_ok:
        before_to_after = _heuristic_before_to_after(before, after)

    n_before = _memory_interaction_count(before)
    n_after = _memory_interaction_count(after)
    _fill_identity_map(before_to_after, n_before, n_after)

    before_info = fetch_info_json(before_path)
    after_info = fetch_info_json(after_path)
    before_extract = fetch_extract_json(before_path)
    after_extract = fetch_extract_json(after_path)
    before_solve = fetch_solve_json_all(before_path, present=present)
    after_solve = fetch_solve_json_all(after_path, present=present)

    before_state = _analyze_side(
        before,
        before_path,
        solve=before_solve,
        info=before_info,
        extract=before_extract,
        align_rows=before_align_rows,
    )
    after_state = _analyze_side(
        after,
        after_path,
        solve=after_solve,
        info=after_info,
        extract=after_extract,
    )
    before_matches, before_status = _finalize_side(before_state)
    after_matches, after_status = _finalize_side(after_state)

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
        before_status=before_status,
        after_status=after_status,
    )
