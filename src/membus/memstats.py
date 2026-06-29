"""Statistics over the memory bus of one circuit.

Per address space: interaction count, send/recv split & balance, symbolic vs
concrete keys, distinct keys / alias classes, and whether the space partitions
cleanly (no static aliasing). Plus the two extraction preconditions for the
whole memory bus: are all send timestamps totally ordered, and is every recv
bounded below its own send.
"""
from __future__ import annotations

import collections
from dataclasses import dataclass
from typing import Any

from src.lens.loader import machine_of
from src.lens.metrics import mem_key_symbolic, mult_kind

from . import keys, order
from .busfmt import memory_bis


@dataclass
class ASStats:
    """One address space's memory-bus summary."""
    addr_space: str        # "1", "2", … or "sym" (symbolic address space)
    count: int
    send: int
    recv: int
    other: int
    sym_key: int
    concrete_key: int
    distinct_keys: int
    determined: bool       # alias sets statically decidable?
    reason: str

    @property
    def balanced(self) -> bool:
        return self.send == self.recv

    def as_dict(self) -> dict[str, Any]:
        return {
            "address_space": self.addr_space, "count": self.count,
            "send": self.send, "recv": self.recv, "other": self.other,
            "balanced": self.balanced, "sym_key": self.sym_key,
            "concrete_key": self.concrete_key, "distinct_keys": self.distinct_keys,
            "alias_determined": self.determined, "alias_reason": self.reason,
        }


@dataclass
class MemStats:
    mem_id: int
    n_memory: int
    address_spaces: list[ASStats]
    sends_ordered: bool
    recvs_bounded: bool

    def as_dict(self) -> dict[str, Any]:
        return {
            "mem_id": self.mem_id, "n_memory": self.n_memory,
            "address_spaces": [a.as_dict() for a in self.address_spaces],
            "preconditions": {
                "sends_totally_ordered": self.sends_ordered,
                "recvs_bounded": self.recvs_bounded,
            },
        }


def compute(data: Any, mem_id: int = 1) -> MemStats:
    machine = machine_of(data)
    bis = memory_bis(data, mem_id)
    if "constraints" in machine and "bus_interactions" in machine:
        edges, recv_bound, _ = order.deduce(machine)
        chain = set(order.total_order(machine, edges))
    else:
        recv_bound, chain = {}, set()

    groups: dict[str, list[dict]] = collections.defaultdict(list)
    for b in bis:
        a = keys.address_space_of(b)
        groups["sym" if a is None else str(a)].append(b)

    as_list: list[ASStats] = []
    for asv, grp in sorted(groups.items()):
        send = recv = other = sym_key = 0
        ks: list[keys.Key] = []
        for b in grp:
            mk = mult_kind(b["mult"])
            send += mk == "send"
            recv += mk == "recv"
            other += mk not in ("send", "recv")
            sym_key += mem_key_symbolic(b)
            ks.append(keys.recover_key(machine, b))
        det, reason = keys.classify_address_space(ks)
        as_list.append(ASStats(asv, len(grp), send, recv, other, sym_key,
                               len(grp) - sym_key, len(set(ks)), det, reason))

    sends_ordered = recvs_bounded = True
    for b in bis:
        mk = mult_kind(b["mult"])
        tscol = order.ts_col(b["args"][6])
        if mk == "send":
            if not (tscol and order.is_fs(tscol) and tscol in chain):
                sends_ordered = False
        elif mk == "recv":
            if not (tscol and order.is_prev(tscol) and tscol in recv_bound):
                recvs_bounded = False
    return MemStats(mem_id, len(bis), as_list, sends_ordered, recvs_bounded)
