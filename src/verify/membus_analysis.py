"""Structured memory-bus analysis for plain permutation encoding."""
from __future__ import annotations

import collections
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
    fetch_solve_json,
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
    interior_partners: set[int] = field(default_factory=set)


@dataclass
class SideState:
    n: int
    facts: list[IdFacts]
    matches: list[set[int]]
    status: list[list[Tri]]


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


def _ordered_ts_pairs(order_edges: list[dict]) -> set[frozenset[str]]:
    nodes = sorted({e["lhs"] for e in order_edges} | {e["rhs"] for e in order_edges})
    if not nodes:
        return set()
    idx = {n: i for i, n in enumerate(nodes)}
    n = len(nodes)
    before = [[False] * n for _ in range(n)]
    for e in order_edges:
        before[idx[e["lhs"]]][idx[e["rhs"]]] = True
    for k in range(n):
        for i in range(n):
            if not before[i][k]:
                continue
            for j in range(n):
                before[i][j] = before[i][j] or before[k][j]
    return {
        frozenset({nodes[i], nodes[j]})
        for i in range(n)
        for j in range(i + 1, n)
        if before[i][j] or before[j][i]
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


def _status_tuple(st: list[Tri]) -> Status:
    return Status(st[0], st[1], st[2], st[3])


def _ingest_side(
    data: dict,
    path: Path,
    *,
    solve: dict | None,
    info: dict | None,
    extract: dict | None,
) -> SideState:
    mem_id = _memory_bus_id(data)
    assert mem_id is not None
    n = _memory_interaction_count(data)
    facts = [IdFacts() for _ in range(n)]
    mults = _json_mult_const(data, mem_id)

    if info:
        for raw in info.get("interactions") or []:
            o = raw.get("ordinal")
            if o is None or o >= n:
                continue
            f = facts[o]
            if raw.get("kind"):
                f.kind = raw["kind"]
            as_raw = raw.get("address_space")
            if as_raw is not None and as_raw != "sym":
                f.addr_space = int(as_raw)
            if raw.get("key"):
                f.key = parse_membus_key(raw["key"])
            t = _parse_time(raw.get("time"))
            if t is not None:
                f.time = t

    if extract:
        ts_by_ord = {
            r["ordinal"]: r["abstract_ts"]
            for r in extract.get("interactions") or []
            if r.get("ordinal") is not None
        }
        for o, ts in ts_by_ord.items():
            if o < n:
                facts[o].abstract_ts = ts

    if solve:
        for raw in solve.get("interactions") or []:
            o = raw.get("ordinal")
            if o is None or o >= n:
                continue
            f = facts[o]
            if raw.get("kind") and not f.kind:
                f.kind = raw["kind"]
            if raw.get("key") and not f.key:
                f.key = parse_membus_key(raw["key"])
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

    for o in range(n):
        if o < len(mults):
            facts[o].mult_const = mults[o]

    matches = [set(range(n)) for _ in range(n)]
    status = [[None, None, None, None] for _ in range(n)]

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

        match f.solve_io:
            case "in":
                _set_flag(status[i], 1, False)
                _set_flag(status[i], 3, False)
            case "out":
                _set_flag(status[i], 0, False)
                _set_flag(status[i], 3, False)

    return SideState(n=n, facts=facts, matches=matches, status=status)


def _rule_out_pairs(state: SideState, ordered_ts: set[frozenset[str]]) -> None:
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
        if tai and taj and frozenset({tai, taj}) in ordered_ts:
            _remove_match(state, i, j)


def _remove_match(state: SideState, i: int, j: int) -> None:
    state.matches[i].discard(j)
    state.matches[j].discard(i)


def _restrict_partners(state: SideState) -> None:
    p = ARGS().field_type.value
    for i, f in enumerate(state.facts):
        if not f.interior_partners:
            continue
        # The self-match m(i,i) covers the disabled/input/output cases. It is
        # only truly ruled out when the multiplicity is a non-zero constant:
        # then the row can never be disabled (is_valid == 0 would still leave
        # mult != 0), so it is genuinely interior. For an is_valid-gated
        # multiplicity the row is disabled (and self-matches) when is_valid == 0,
        # so the self-match must be kept.
        self_ruled_out = f.mult_const is not None and f.mult_const % p != 0
        allowed = set(f.interior_partners)
        if not self_ruled_out:
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
    return changed


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
    order_edges: list[dict],
) -> tuple[list[set[int]], list[Status]]:
    state = _ingest_side(data, path, solve=solve, info=info, extract=extract)
    ordered_ts = _ordered_ts_pairs(order_edges)
    _rule_out_pairs(state, ordered_ts)
    _restrict_partners(state)
    _run_worklist(state)
    return _finalize_side(state)


def run_membus_analysis(
    before: dict[str, Any],
    after: dict[str, Any],
    before_path: Path,
    after_path: Path,
) -> MembusAnalysis:
    before = _normalize_dump(before)
    after = _normalize_dump(after)
    before_to_after: dict[int, int] = {}
    align_ok = False
    present = _memory_address_spaces(before)

    for addr_space in (1, 2):
        if present is not None and addr_space not in present:
            continue
        al = fetch_align_json(before_path, after_path, addr_space=addr_space)
        if al is None:
            continue
        align_ok = True
        for raw in al.get("interactions") or []:
            aid = raw.get("after_id")
            bid = raw.get("before_id")
            if aid is not None and bid is not None and raw.get("status") == "kept":
                before_to_after[bid] = aid

    if not align_ok:
        before_to_after = _heuristic_before_to_after(before, after)

    n_before = _memory_interaction_count(before)
    n_after = _memory_interaction_count(after)
    _fill_identity_map(before_to_after, n_before, n_after)

    before_info = fetch_info_json(before_path)
    after_info = fetch_info_json(after_path)
    before_extract = fetch_extract_json(before_path)
    after_extract = fetch_extract_json(after_path)
    before_solve = fetch_solve_json(before_path, addr_space=1)
    after_solve = fetch_solve_json(after_path, addr_space=1)

    before_edges = (before_extract or {}).get("order_edges") or []
    after_edges = (after_extract or {}).get("order_edges") or []

    before_matches, before_status = _analyze_side(
        before,
        before_path,
        solve=before_solve,
        info=before_info,
        extract=before_extract,
        order_edges=before_edges,
    )
    after_matches, after_status = _analyze_side(
        after,
        after_path,
        solve=after_solve,
        info=after_info,
        extract=after_extract,
        order_edges=after_edges,
    )

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
