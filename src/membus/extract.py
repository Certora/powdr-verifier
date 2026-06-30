"""Extract a memory bus into busat ``.bus`` format with an ABSTRACT timestamp order.

Algorithm (a)/(b)/(c):
  (a) abstract each op's timestamp arg to one symbol ``ts_i`` (the concrete
      timestamp never appears in the MEM rows);
  (b) infer the order over the ``ts_i``, each edge justified — intra-instruction
      from the offset constants, cross-instruction from R1 (the from_state
      chain), and ``recv < its own-op send`` from R2 (the LessThan gadget);
  (c) emit the abstract ``ts_i`` in MEM rows plus the justified ``<`` edges.

Keys are emitted as constant literals (concrete) or ``base + offset`` DEFS
(symbolic). With a ``post`` circuit, only the **removed** interactions (the set
a pass eliminated) are extracted. Ported from ``busat/tools/dump_to_bus_abstract.py``.
"""
from __future__ import annotations

import collections
from typing import Any

from src.lens.loader import machine_of
from src.lens.normalize import to_signed

from . import keys, order
from .busfmt import Emitter, find_duplicates, memory_bis, removed_memory_bis


def _offset_of(arg: Any) -> int:
    """Intra-instruction offset constant in a send ts expr ``from_state_K + off``."""
    off = 0
    if isinstance(arg, list) and len(arg) == 3 and arg[1] == "+":
        for side in (arg[0], arg[2]):
            if isinstance(side, int):
                off += to_signed(side)
    return off


def build(pre: dict, mem_id: int, addr_space: int | None, post: dict | None) -> str:
    """Emit the busat ``.bus`` text for the memory bus of ``pre``.

    ``post`` given ⟹ extract only the interactions removed (``pre − post``).
    ``addr_space`` given ⟹ restrict to that address space.
    """
    pre = machine_of(pre)
    if post is not None:
        post = machine_of(post)
    rows = removed_memory_bis(pre, post, mem_id) if post is not None else memory_bis(pre, mem_id)
    if addr_space is not None:
        rows = [b for b in rows
                if isinstance(b["args"][0], int) and to_signed(b["args"][0]) == addr_space]
    if not rows:
        raise ValueError(f"no memory interactions (id={mem_id}, as={addr_space})")
    dups = find_duplicates(rows)
    if dups:
        raise ValueError(
            f"{len(dups)} duplicated memory interaction(s) — a sound memory bus has "
            f"none (each access has a unique timestamp); the abstract bus would be "
            f"ill-defined. First: {dups[0][1]}× {dups[0][0]}")

    edges_R1, recv_bound, _nonneg = order.deduce(pre)
    chain = order.total_order(pre, edges_R1)
    access_rank = {}
    for pos, fscol in enumerate(chain):
        k = order.access_index(fscol)
        if k is not None:
            access_rank[k] = pos

    em = Emitter()
    by_ptr: dict[str, list[dict]] = collections.defaultdict(list)
    for b in rows:
        by_ptr[em.expr_str(b["args"][1])].append(b)
    ptr_atom: dict[str, str] = {}
    for pexpr, lst in by_ptr.items():
        k = keys.recover_key(pre, lst[0])
        if isinstance(k, keys.BaseOffset):
            var = f"ptr_{k.base}_{k.offset}"
            ptr_atom[pexpr] = var
            em.defs.setdefault(var, f"BASE_{k.base} + {k.offset}")
        else:                       # Const -> integer literal; Unresolved -> free pointer var
            ptr_atom[pexpr] = em.atom(lst[0]["args"][1], "ptr")

    # (a) one abstract symbol per distinct timestamp expression
    ts_sym: dict[str, str] = {}

    def tsym(arg: Any) -> str:
        key = em.expr_str(arg)
        if key not in ts_sym:
            ts_sym[key] = f"ts{len(ts_sym)}"
        return ts_sym[key]

    sends_by_k: dict[int, list[tuple[int, str]]] = collections.defaultdict(list)
    recvs_by_k: dict[int, list[tuple[int | None, str]]] = collections.defaultdict(list)
    mem_lines = []
    for i, b in enumerate(rows):
        a = b["args"]
        mult = to_signed(b["mult"]) if isinstance(b["mult"], int) else None
        if mult not in (-1, 0, 1):
            raise ValueError(f"interaction {i}: mult {mult} not in -1/0/1")
        sym = tsym(a[6])
        tscol = order.ts_col(a[6])
        k = order.access_index(tscol) if tscol else None
        if mult == 1:
            sends_by_k[k].append((_offset_of(a[6]), sym))
        elif mult == -1:
            const = recv_bound[tscol][2] if tscol in recv_bound else None
            recvs_by_k[k].append((const, sym))
        addr = em.atom(a[0], "as")
        ptr = ptr_atom[em.expr_str(a[1])]
        data = [em.atom(a[j], f"b{j - 2}") for j in range(2, 6)]
        mem_lines.append(f"{i}: {mult}, {addr}, {ptr}, " + ", ".join(data) + f", {sym}")

    # (b) inferred order edges, each justified
    edges: list[tuple[str, str, str]] = []
    for k, sends in sends_by_k.items():
        ss = sorted(sends)
        for (o1, s1), (o2, s2) in zip(ss, ss[1:]):
            edges.append((s1, s2, f"intra-instr K={k}: offset {o1} < {o2}"))
    ks = sorted([k for k in sends_by_k if k in access_rank], key=lambda k: access_rank[k])
    for ka, kb in zip(ks, ks[1:]):
        last = sorted(sends_by_k[ka])[-1][1]
        first = sorted(sends_by_k[kb])[0][1]
        edges.append((last, first, f"R1 from_state chain: K={ka} < K={kb}"))
    for k, recvs in recvs_by_k.items():
        sends = sorted(sends_by_k.get(k, []))
        rs = sorted(recvs, key=lambda t: (t[0] if t[0] is not None else -10**9))
        for j, (c, rsym) in enumerate(rs):
            if sends:
                own = sends[min(j, len(sends) - 1)][1]
                edges.append((rsym, own, f"R2 LessThan: recv(K={k},const={c}) < own send"))

    # (c) emit
    out = ["MEM", *mem_lines, ""]
    if em.defs:
        out.append("DEFS")
        out += [f"{v} := {em.defs[v]}" for v in sorted(em.defs)]
        out.append("")
    out.append("CONSTRAINTS")
    for lhs, rhs, why in edges:
        out.append(f"# {why}")
        out.append(f"{lhs} < {rhs}")
    out.append("")
    return "\n".join(out)
