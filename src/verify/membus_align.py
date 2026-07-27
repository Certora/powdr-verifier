"""Memory-bus alignment from ``membus align`` / ``info`` / ``solve``."""
from __future__ import annotations

import logging
from pathlib import Path
from typing import Any

from .membus_subprocess import fetch_align_json, fetch_info_json, fetch_solve_json_all
from .membus_types import AlignRowInfo, MembusAlignment, parse_membus_key

_LOG = logging.getLogger(__name__)


def _memory_bus_id(data: dict) -> int | None:
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    for bid, btype in bus_ids.items():
        if btype == "Memory":
            return int(bid)
    return None


def _memory_interaction_count(data: dict) -> int:
    mem_id = _memory_bus_id(data)
    if mem_id is None:
        return 0
    return sum(
        1 for bi in data["machine"]["bus_interactions"] if bi["id"] == mem_id
    )


def _memory_address_spaces(data: dict) -> set[int] | None:
    """Constant address spaces present among memory interactions.

    Returns ``None`` if we cannot determine the set (symbolic address space or
    unresolved memory bus), signalling that no space should be skipped.
    """
    mem_id = _memory_bus_id(data)
    if mem_id is None:
        return None
    spaces: set[int] = set()
    for bi in data["machine"]["bus_interactions"]:
        if bi["id"] != mem_id:
            continue
        a = bi["args"][0]
        if isinstance(a, int):
            spaces.add(a)
        else:
            return None
    return spaces


def _heuristic_before_to_after(before: dict, after: dict) -> dict[int, int]:
    mem_id = _memory_bus_id(before)
    assert mem_id is not None
    before_list = [
        bi for bi in before["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    after_list = [
        bi for bi in after["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    nb, na = len(before_list), len(after_list)
    if nb == 0 or na == 0:
        return {}
    if nb == na:
        return {i: i for i in range(nb)}

    before_json = {i: before_list[i] for i in range(nb)}
    after_json = {j: after_list[j] for j in range(na)}
    before_to_after: dict[int, int] = {}
    d = nb - na

    for b in range(nb):
        if b in before_to_after:
            continue
        lo_w = max(0, b - d)
        hi_w = min(na - 1, b)
        for bb in range(b - 1, -1, -1):
            if bb in before_to_after:
                lo_w = max(lo_w, before_to_after[bb] + 1)
                break
        for bb in range(b + 1, nb):
            if bb in before_to_after:
                hi_w = min(hi_w, before_to_after[bb] - 1)
                break
        used_a = set(before_to_after.values())
        for a in range(lo_w, hi_w + 1):
            if a in used_a:
                continue
            if before_json[b] == after_json[a]:
                before_to_after[b] = a
                break

    for b in range(nb):
        if b in before_to_after:
            continue
        if b == 0 and 1 in before_to_after and before_to_after[1] == 1:
            before_to_after[0] = 0
            continue
        if b == nb - 1 and nb - 2 in before_to_after and before_to_after[nb - 2] == na - 2:
            before_to_after[nb - 1] = na - 1
            continue
        if b == 0 or b == nb - 1:
            continue
        if (
            b - 1 in before_to_after
            and b + 1 in before_to_after
            and before_to_after[b - 1] + 2 == before_to_after[b + 1]
        ):
            before_to_after[b] = before_to_after[b - 1] + 1

    return before_to_after


def _row_or_new(rows: dict[int, AlignRowInfo], ordn: int) -> AlignRowInfo:
    if ordn not in rows:
        rows[ordn] = AlignRowInfo()
    return rows[ordn]


def _merge_align_row(rows: dict[int, AlignRowInfo], raw: dict) -> None:
    ordn = raw.get("before_id")
    if ordn is None:
        return
    row = _row_or_new(rows, ordn)
    for attr in ("kind", "status", "local_role"):
        if raw.get(attr):
            setattr(row, attr, raw[attr])
    if raw.get("key"):
        row.key = parse_membus_key(raw["key"]) or row.key
    partners = raw.get("local_partners")
    if partners is not None:
        row.local_partners = list(partners)
    io = raw.get("io")
    if io == "in" and not row.local_role:
        row.local_role = "input"
    elif io == "out" and not row.local_role:
        row.local_role = "output"


def _merge_info_rows(rows: dict[int, AlignRowInfo], info: dict) -> None:
    for raw in info.get("interactions") or []:
        ordn = raw.get("ordinal")
        if ordn is None:
            continue
        row = _row_or_new(rows, ordn)
        if raw.get("kind"):
            row.kind = raw["kind"]
        if raw.get("key"):
            row.key = parse_membus_key(raw["key"]) or row.key


def _local_role_from_solve(raw: dict) -> tuple[str | None, list[int]]:
    kind = raw.get("kind")
    if kind == "disabled":
        return "inert", []
    io = raw.get("io")
    if io == "in":
        return "input", []
    if io == "out":
        return "output", []
    reads_from = raw.get("reads_from")
    if reads_from is not None:
        return "interior", [reads_from]
    read_by = raw.get("read_by")
    if read_by:
        partners = read_by if isinstance(read_by, list) else [read_by]
        return "interior", list(partners)
    return None, []


def _row_has_local(row: AlignRowInfo) -> bool:
    if not row.local_role:
        return False
    if row.local_role in ("input", "output", "inert"):
        return True
    return bool(row.local_partners)


def _merge_solve_rows(
    rows: dict[int, AlignRowInfo],
    solve: dict,
    *,
    skip_ordinals: set[int] | None = None,
) -> None:
    skip = skip_ordinals or set()
    for raw in solve.get("interactions") or []:
        ordn = raw.get("ordinal")
        if ordn is None or ordn in skip:
            continue
        row = _row_or_new(rows, ordn)
        if _row_has_local(row):
            continue
        role, partners = _local_role_from_solve(raw)
        if role and not row.local_role:
            row.local_role = role
        if partners and not row.local_partners:
            row.local_partners = partners
        if raw.get("kind") and not row.kind:
            row.kind = raw["kind"]
        if raw.get("key") and not row.key:
            row.key = parse_membus_key(raw["key"]) or row.key


def _transport_after_rows(
    before_rows: dict[int, AlignRowInfo],
    before_to_after: dict[int, int],
) -> dict[int, AlignRowInfo]:
    after_rows: dict[int, AlignRowInfo] = {}
    inv = {a: b for b, a in before_to_after.items()}
    for after_ord, before_ord in inv.items():
        br = before_rows.get(before_ord)
        if br is None:
            continue
        partners = [
            before_to_after[p]
            for p in br.local_partners
            if p in before_to_after
        ]
        after_rows[after_ord] = AlignRowInfo(
            kind=br.kind,
            key=br.key,
            local_role=br.local_role,
            local_partners=partners,
            status="kept",
        )
    return after_rows


def _fill_identity_map(
    before_to_after: dict[int, int], n_before: int, n_after: int
) -> None:
    if n_before != n_after:
        return
    for i in range(n_before):
        before_to_after.setdefault(i, i)


def run_membus_alignment(
    before: dict[str, Any],
    after: dict[str, Any],
    before_path: Path,
    after_path: Path,
) -> MembusAlignment:
    before_rows: dict[int, AlignRowInfo] = {}
    after_rows: dict[int, AlignRowInfo] = {}
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
            _merge_align_row(before_rows, raw)
            aid = raw.get("after_id")
            bid = raw.get("before_id")
            if aid is not None and bid is not None and raw.get("status") == "kept":
                before_to_after[bid] = aid

    if not align_ok:
        before_to_after = _heuristic_before_to_after(before, after)
    else:
        after_rows = _transport_after_rows(before_rows, before_to_after)

    for path, rows in ((before_path, before_rows), (after_path, after_rows)):
        info = fetch_info_json(path)
        if info is not None:
            _merge_info_rows(rows, info)

    n_before = _memory_interaction_count(before)
    n_after = _memory_interaction_count(after)
    _fill_identity_map(before_to_after, n_before, n_after)

    solve_skip_before = {o for o, r in before_rows.items() if _row_has_local(r)}
    solve_skip_after = {o for o, r in after_rows.items() if _row_has_local(r)}
    for path, rows, skip in (
        (before_path, before_rows, solve_skip_before),
        (after_path, after_rows, solve_skip_after),
    ):
        solve = fetch_solve_json_all(path, present=present)
        if solve is not None:
            _merge_solve_rows(rows, solve, skip_ordinals=skip)

    for _, rows, n in (
        (before_path, before_rows, n_before),
        (after_path, after_rows, n_after),
    ):
        for i in range(n):
            _row_or_new(rows, i)

    _LOG.info(
        "membus alignment: n_before=%d n_after=%d aligned_pairs=%d "
        "before_rows=%d after_rows=%d",
        n_before,
        n_after,
        len(before_to_after),
        len(before_rows),
        len(after_rows),
    )
    return MembusAlignment(
        before_path=before_path,
        after_path=after_path,
        before_to_after=before_to_after,
        before_rows=before_rows,
        after_rows=after_rows,
    )
