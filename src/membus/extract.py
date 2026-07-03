"""Extract a memory bus into busat ``.bus`` format with an ABSTRACT timestamp order.

Algorithm (a)/(b)/(c):
  (a) abstract each op's timestamp arg to one symbol ``ts_i`` (the concrete
      timestamp never appears in the MEM rows);
  (b) infer the order over the ``ts_i``, **every edge justified by a fact**;
  (c) emit the abstract ``ts_i`` in MEM rows plus the justified ``<`` edges.

Edge derivation (this is where the old positional j-th-recv ↔ j-th-send
heuristic used to live; edges are now derived, never guessed):

- **send < send**: when both sends have a resolved virtual time (Gap-fact
  chain base + syntactic intra offset), consecutive sends in global vtime
  order get an edge — justified by the vtime arithmetic. Without a verified
  total order, only sends sharing a from_state column are compared (their
  gap is the syntactic offset difference).
- **recv < send**: a recv with RecvUpper facts has ``prev_ts ≤ threshold``
  (minimum over its facts). It precedes exactly the sends with
  ``vtime > threshold``; one edge to the **earliest** such send is emitted
  (the rest follow through the send chain). A recv with no justified bound
  gets NO edge — the omission is reported, not papered over.

Keys are emitted as constant literals (concrete) or ``base + offset`` DEFS
(symbolic, from certified AffineDef facts). With a ``post`` circuit, only the
**removed** interactions (the multiset a pass eliminated) are extracted.
"""
from __future__ import annotations

import collections
from typing import Any

from . import keys, order
from .busfmt import Emitter
from .busmodel import MemRow, find_duplicates, memory_rows, removed_rows
from .rules import Analysis


def build_dict(pre: dict, mem_id: int, addr_space: int | None, post: dict | None,
               assume_is_valid: bool = True) -> dict:
    """Structured extract result for JSON export and match-var preanalysis.

    Returns ``interactions`` (ordinal + abstract_ts), ``order_edges``
    (lhs/rhs/why), ``unordered`` (abstract ts symbols with no justified edge),
    plus ``_mem_lines`` / ``_defs`` for :func:`format_bus`.
    """
    an = Analysis(pre, mem_id, assume_is_valid)
    rows = an.mem
    if post is not None:
        rows = removed_rows(rows, memory_rows(post, mem_id))
    if addr_space is not None:
        rows = [r for r in rows if r.addr_space == addr_space]
    if not rows:
        raise ValueError(f"no memory interactions (id={mem_id}, as={addr_space})")
    dups = find_duplicates(rows)
    if dups:
        raise ValueError(
            f"{len(dups)} duplicated memory interaction(s) -- a sound memory bus has "
            f"none (each access has a unique timestamp); the abstract bus would be "
            f"ill-defined. First: {dups[0][1]}x {dups[0][0]}")

    soff = order.send_offsets(an)

    em = Emitter()
    # keys: one atom per distinct pointer expression
    ptr_atom: dict[str, str] = {}
    ptr_key: dict[str, keys.Key] = {}
    for row in rows:
        pexpr = em.expr_str(row.ptr)
        if pexpr in ptr_key:
            continue
        k = keys.recover_key(an, row)
        ptr_key[pexpr] = k
        if isinstance(k, keys.BaseOffset):
            var = f"ptr_{k.base}_{k.offset}"
            ptr_atom[pexpr] = var
            em.defs.setdefault(var, f"BASE_{k.base} + {k.offset}")
        else:
            ptr_atom[pexpr] = em.atom(row.ptr, "ptr")

    ts_sym: dict[str, str] = {}

    def tsym(arg: Any) -> str:
        key = em.expr_str(arg)
        if key not in ts_sym:
            ts_sym[key] = f"ts{len(ts_sym)}"
        return ts_sym[key]

    # sends: vtime-resolved and unresolved-but-sharing-a-base
    send_vt: list[tuple[int, str]] = []                  # (vtime, sym) — resolved
    send_by_fs: dict[str, list[tuple[int, str]]] = collections.defaultdict(list)
    send_unresolved: list[str] = []                      # syms with no vtime
    recv_rows: list[tuple[MemRow, str]] = []
    seen_send_syms: set[str] = set()

    class_id: dict[tuple[str, str], int] = {}
    as_keys: dict[str, list[keys.Key]] = collections.defaultdict(list)
    interactions: list[dict[str, Any]] = []
    mem_lines: list[str] = []
    for i, row in enumerate(rows):
        kf = an.kinds.get(row.ordinal)
        if kf is None:
            raise ValueError(f"interaction {i}: unresolved multiplicity {row.mult!r} "
                             f"(not send / recv / disabled)")
        mult = {"send": 1, "recv": -1, "disabled": 0}[kf.kind]
        sym = tsym(row.ts)
        tscol = order.ts_col(row.ts)
        if kf.kind == "send" and sym not in seen_send_syms:
            seen_send_syms.add(sym)
            off = order.intra_offset(row.ts)
            if tscol is not None:
                base = soff.get(tscol)
                if base is not None:
                    send_vt.append((base + off, sym))
                else:
                    send_unresolved.append(sym)
                send_by_fs[tscol].append((off, sym))
            else:
                send_unresolved.append(sym)
        elif kf.kind == "recv":
            recv_rows.append((row, sym))
        addr = em.atom(row.addr_space_expr, "as")
        pexpr = em.expr_str(row.ptr)
        ptr = ptr_atom[pexpr]
        rk = ptr_key[pexpr]
        asv = "sym" if row.addr_space is None else str(row.addr_space)
        key = str(rk)
        as_keys[asv].append(rk)
        cid = class_id.setdefault((asv, key), len(class_id))
        data = [em.atom(row.data[j], f"b{j}") for j in range(4)]
        line = f"{i}: {mult}, {addr}, {ptr}, " + ", ".join(data) + f", {sym}"
        mem_lines.append(line)
        interactions.append({
            "ordinal": row.ordinal,
            "abstract_ts": sym,
            "address_space": asv,
            "key": key,
            "alias_class": cid,
        })

    as_det = {asv: keys.classify_address_space(ks)[0] for asv, ks in as_keys.items()}
    for r in interactions:
        r["alias_determined"] = as_det[r["address_space"]]

    raw_edges: list[tuple[str, str, str]] = []
    ordered_syms: set[str] = set()

    # send < send: consecutive in global vtime order (resolved sends)
    send_vt.sort()
    for (v1, s1), (v2, s2) in zip(send_vt, send_vt[1:]):
        if v1 < v2:
            raw_edges.append((s1, s2, f"send chain: vtime T+{v1} < T+{v2}"))
            ordered_syms.update((s1, s2))
    # sends with unresolved chain base but a shared from_state column: the gap
    # is the syntactic offset difference — justified without any Gap fact.
    if not send_vt:
        for fs, offs in send_by_fs.items():
            offs.sort()
            for (o1, s1), (o2, s2) in zip(offs, offs[1:]):
                if o1 < o2:
                    raw_edges.append((s1, s2, f"same base {fs}: offset {o1} < {o2}"))
                    ordered_syms.update((s1, s2))

    # recv < send: minimum RecvUpper threshold, edge to the earliest later send
    unordered: list[dict[str, str]] = [
        {"abstract_ts": s, "why": "send timestamp has no resolved virtual time"}
        for s in send_unresolved if s not in ordered_syms]
    for row, rsym in recv_rows:
        tscol = order.ts_col(row.ts)
        facts = an.recv_uppers.get(tscol, []) if tscol else []
        threshold = None
        for f in facts:
            base = soff.get(f.fs)
            if base is None:
                continue
            t = base + f.const
            threshold = t if threshold is None else min(threshold, t)
        if threshold is None:
            unordered.append({"abstract_ts": rsym,
                              "why": "recv has no justified LessThan bound"})
            continue
        later = [(v, s) for v, s in send_vt if v > threshold]
        if not later:
            unordered.append({"abstract_ts": rsym,
                              "why": f"recv bound T+{threshold} not before any send"})
            continue
        v, ssym = min(later)
        raw_edges.append((rsym, ssym,
                          f"RecvUpper: prev_ts <= T+{threshold} < T+{v} (earliest later send)"))
        ordered_syms.add(rsym)

    order_edges = [{"lhs": a, "rhs": b, "why": why} for a, b, why in raw_edges]
    return {
        "interactions": interactions,
        "order_edges": order_edges,
        "unordered": unordered,
        "_mem_lines": mem_lines,
        "_defs": dict(em.defs),
    }


def format_bus(model: dict) -> str:
    """Render a :func:`build_dict` result as busat ``.bus`` text."""
    out = ["MEM", *model["_mem_lines"], ""]
    defs = model["_defs"]
    if defs:
        out.append("DEFS")
        out += [f"{v} := {defs[v]}" for v in sorted(defs)]
        out.append("")
    out.append("CONSTRAINTS")
    for e in model["order_edges"]:
        if "why" in e:
            out.append(f"# {e['why']}")
        out.append(f"{e['lhs']} < {e['rhs']}")
    for u in model.get("unordered", []):
        out.append(f"# UNORDERED {u['abstract_ts']}: {u['why']}")
    out.append("")
    return "\n".join(out)


def build(pre: dict, mem_id: int, addr_space: int | None, post: dict | None,
          assume_is_valid: bool = True) -> str:
    """Emit the busat ``.bus`` text for the memory bus of ``pre``.

    ``post`` given ⟹ extract only the interactions removed (``pre − post``).
    ``addr_space`` given ⟹ restrict to that address space.
    """
    return format_bus(build_dict(pre, mem_id, addr_space, post, assume_is_valid))


def extract_json(model: dict) -> dict:
    """Public JSON subset (drops internal ``_`` keys)."""
    return {k: v for k, v in model.items() if not k.startswith("_")}
