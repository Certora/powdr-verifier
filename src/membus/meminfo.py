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

from . import keys, naming, order
from .linform import linform
from .rules import Analysis


@dataclass
class InfoRow:
    ordinal: int           # membus ordinal (k-th id==mem_id interaction)
    kind: str              # send / recv / disabled / sym / other
    addr_space: str
    key: str               # str(Key): "const 8" | "rs1_0+40" | "unresolved(...)"
    time: str              # base+offset form: send "T+12", recv "≤T+12", else ts col
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


def _display_kind(an: Analysis, ordinal: int, mult: Any) -> str:
    k = an.kinds.get(ordinal)
    if k is not None:
        return k.kind
    return "sym" if linform(mult) is None else "other"


def compute(data: Any, mem_id: int = 1, addr_space: int | None = None) -> list[InfoRow]:
    an = Analysis(data, mem_id)
    have_machine = "constraints" in an.machine and "bus_interactions" in an.machine
    chain = (order.total_send_order(an) or []) if have_machine else []
    soff = order.send_offsets(an) if have_machine else {}
    pos = {col: i for i, col in enumerate(chain)}

    def _t(n: int) -> str:
        return f"T+{n}" if n >= 0 else f"T{n}"

    class_id: dict[tuple[str, str], int] = {}
    rows: list[InfoRow] = []
    for r in an.mem:
        asv = "sym" if r.addr_space is None else str(r.addr_space)
        if addr_space is not None and asv != str(addr_space):
            continue
        kind = _display_kind(an, r.ordinal, r.mult)
        key = keys.recover_key(an, r)
        tscol = order.ts_col(r.ts) or ""
        if naming.is_fs(tscol):                      # a send: occurs AT T + (chain offset + intra)
            order_pos = pos.get(tscol)
            base = soff.get(tscol)
            time = _t(base + order.intra_offset(r.ts)) if base is not None else tscol
        elif tscol in an.recv_uppers:                # a recv: prev_ts ≤ min threshold
            best_fs, best_t = None, None
            for f in an.recv_uppers[tscol]:
                base = soff.get(f.fs)
                if base is None:
                    continue
                t = base + f.const
                if best_t is None or t < best_t:
                    best_fs, best_t = f.fs, t
            if best_t is not None:
                order_pos, time = pos.get(best_fs), f"≤{_t(best_t)}"
            else:
                f0 = an.recv_uppers[tscol][0]
                order_pos, time = pos.get(f0.fs), f"≤{f0.fs}"
        else:
            order_pos, time = None, tscol
        cid = class_id.setdefault((asv, str(key)), len(class_id))
        rows.append(InfoRow(r.ordinal, kind, asv, str(key), time, tscol, order_pos,
                            order.access_index(tscol) if tscol else None, cid))
    return rows
