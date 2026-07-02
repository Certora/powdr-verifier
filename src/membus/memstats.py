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

from src.lens.metrics import mem_key_symbolic, mult_kind

from . import keys, naming, order
from .busmodel import find_duplicates, symbolic_as_ordinals
from .rules import Analysis


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
    duplicates: int        # interactions identical in every field (should be 0)
    symbolic_as: int       # interactions with a non-constant address space (should be 0)

    def as_dict(self) -> dict[str, Any]:
        return {
            "mem_id": self.mem_id, "n_memory": self.n_memory,
            "address_spaces": [a.as_dict() for a in self.address_spaces],
            "preconditions": {
                "sends_totally_ordered": self.sends_ordered,
                "recvs_bounded": self.recvs_bounded,
                "no_duplicates": self.duplicates == 0,
                "duplicates": self.duplicates,
                "solved_as_form": self.symbolic_as == 0,
                "symbolic_as": self.symbolic_as,
            },
        }


def compute(data: Any, mem_id: int = 1) -> MemStats:
    an = Analysis(data, mem_id)
    have_machine = "constraints" in an.machine and "bus_interactions" in an.machine
    chain = set(order.total_send_order(an) or []) if have_machine else set()

    groups: dict[str, list] = collections.defaultdict(list)
    for r in an.mem:
        groups["sym" if r.addr_space is None else str(r.addr_space)].append(r)

    as_list: list[ASStats] = []
    for asv, grp in sorted(groups.items()):
        send = recv = other = sym_key = 0
        ks: list[keys.Key] = []
        for r in grp:
            mk = mult_kind(r.mult)
            send += mk == "send"
            recv += mk == "recv"
            other += mk not in ("send", "recv")
            sym_key += mem_key_symbolic({"args": list(r.args)})
            ks.append(keys.recover_key(an, r))
        det, reason = keys.classify_address_space(ks)
        as_list.append(ASStats(asv, len(grp), send, recv, other, sym_key,
                               len(grp) - sym_key, len(set(ks)), det, reason))

    sends_ordered = recvs_bounded = True
    for r in an.mem:
        mk = mult_kind(r.mult)
        tscol = order.ts_col(r.ts)
        if mk == "send":
            if not (tscol and naming.is_fs(tscol) and tscol in chain):
                sends_ordered = False
        elif mk == "recv":
            if not (tscol and naming.is_prev(tscol) and tscol in an.recv_uppers):
                recvs_bounded = False
    duplicates = sum(c - 1 for _, c in find_duplicates(an.mem))
    return MemStats(mem_id, len(an.mem), as_list, sends_ordered, recvs_bounded,
                    duplicates, len(symbolic_as_ordinals(an.mem)))
