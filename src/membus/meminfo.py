"""Per-interaction detail for the memory bus — the "see aliasing" view.

One row per memory interaction (by membus ordinal): its send/recv kind, address
space, recovered key (const / base+offset / unresolved), timestamp column with
its position in the deduced order and access index, and an alias-class id.
Interactions sharing a class alias (same recovered key); distinct classes are
provably non-aliasing only when the address space is `determined` (see
`memstats`/`keys.classify_address_space`).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.lens.loader import machine_of
from src.lens.metrics import mult_kind

from . import keys, order
from .busfmt import memory_bis


@dataclass
class InfoRow:
    ordinal: int           # membus ordinal (k-th id==mem_id interaction)
    kind: str              # send / recv / sym / other
    addr_space: str
    key: str               # str(Key): "const 8" | "rs1_0+40" | "unresolved(...)"
    time: str              # base+offset form: send "T+12", recv "<T+12", else ts col
    ts_col: str            # the timestamp column (raw)
    order_pos: int | None  # send: position in the send order; recv: position of its own send
    access: int | None     # instruction index K
    alias_class: int       # id shared by interactions with the same (as, key)

    def as_dict(self) -> dict[str, Any]:
        return {
            "ordinal": self.ordinal, "kind": self.kind, "address_space": self.addr_space,
            "key": self.key, "time": self.time, "ts_col": self.ts_col,
            "order_pos": self.order_pos, "access": self.access,
            "alias_class": self.alias_class,
        }


def compute(data: Any, mem_id: int = 1, addr_space: int | None = None) -> list[InfoRow]:
    machine = machine_of(data)
    bis = memory_bis(data, mem_id)
    if "constraints" in machine and "bus_interactions" in machine:
        edges, recv_bound, _ = order.deduce(machine)
        chain = order.total_order(machine, edges)
        soff = order.send_offsets(machine)
    else:
        edges, recv_bound, chain, soff = set(), {}, [], {}
    pos = {col: i for i, col in enumerate(chain)}

    def _t(n: int) -> str:
        return f"T+{n}" if n >= 0 else f"T{n}"

    class_id: dict[tuple[str, str], int] = {}
    rows: list[InfoRow] = []
    for i, b in enumerate(bis):
        a = keys.address_space_of(b)
        asv = "sym" if a is None else str(a)
        if addr_space is not None and asv != str(addr_space):
            continue
        kind = mult_kind(b["mult"])
        key = keys.recover_key(machine, b)
        tsarg = b["args"][6]
        tscol = order.ts_col(tsarg) or ""
        if order.is_fs(tscol):                       # a send: occurs AT T + (chain offset + intra)
            order_pos = pos.get(tscol)
            base = soff.get(tscol)
            time = _t(base + order.intra_offset(tsarg)) if base is not None else tscol
        elif tscol in recv_bound:                    # a recv: prev_ts <= own_send + const (limbs >= 0)
            own_fs, _strict, const = recv_bound[tscol]
            order_pos = pos.get(own_fs)
            base = soff.get(own_fs)
            time = f"≤{_t(base + const)}" if base is not None else f"≤{own_fs}"
        else:
            order_pos, time = None, tscol
        cls_key = (asv, str(key))
        cid = class_id.setdefault(cls_key, len(class_id))
        rows.append(InfoRow(i, kind, asv, str(key), time, tscol, order_pos,
                            order.access_index(tscol) if tscol else None, cid))
    return rows
