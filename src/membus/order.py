"""Deduce the memory-timestamp ORDER from a powdr dump (rules R0/R1/R2).

The matching of memory sends to recvs is fixed by (key, timestamp), and the
timestamps reduce to a pure *order* — which is all the extractor/checker needs.
This module recovers that order from the (timestamp-domain, linear) constraints;
field/data constraints are nonlinear and self-exclude.

- **R0 (nonneg).** A range-checked column is ``>= 0``: any arg of a range-check
  bus (``VariableRangeChecker`` id 3 / ``BitwiseLookup`` 6 / ``TupleRangeChecker``
  7), and the ``*lower_decomp*`` limbs.
- **R1 (send chain).** A linear constraint over only ``from_state`` timestamps
  reduces to ``from_state_b - from_state_a == c`` (or ``>= c``), ``c>0`` ⟹ edge
  ``a -> b``. Transitive closure ⟹ total order on the send timestamps.
- **R2 (recv bound, LessThan gadget).** ``from_state_Y - prev_ts_X - d -
  (nonneg limbs) == 0`` ⟹ (drop the ``>=0`` limbs) ``prev_ts_X <= from_state_Y -
  d`` ⟹ recv_X is before send_Y (its own access's send).

Ported from ``busat/tools/order_rules.py``.
"""
from __future__ import annotations

import collections
import re
from typing import Any

from src.lens.normalize import to_signed


def is_fs(c: str) -> bool:
    """A send timestamp column (the instruction clock ``from_state``)."""
    return "from_state__timestamp_" in c


def is_prev(c: str) -> bool:
    """A recv timestamp column (a ``prev_timestamp`` aux)."""
    return "prev_timestamp" in c


def is_ts(c: str) -> bool:
    return is_fs(c) or is_prev(c)


def names(e: Any, acc: set[str] | None = None) -> set[str]:
    """Collect all column names referenced in an expression."""
    if acc is None:
        acc = set()
    if isinstance(e, str):
        acc.add(e)
    elif isinstance(e, list):
        for x in e:
            names(x, acc)
    return acc


def ts_col(arg: Any) -> str | None:
    """The single timestamp-domain column in a timestamp arg, or None."""
    ts = [c for c in names(arg) if is_ts(c)]
    return ts[0] if len(ts) == 1 else None


def access_index(col: str) -> int | None:
    """Instruction index K from a ``..._<K>@<n>`` timestamp column name."""
    m = re.search(r"_(\d+)@\d+$", col)
    return int(m.group(1)) if m else None


def linterms(e: Any) -> tuple[dict[str, int], int] | None:
    """Linear form ``(coeff_by_col, const)``, or None if nonlinear.

    Constants are signed-normalized. Handles ``+``/``-`` (binary and unary) and
    ``*`` where one side is constant (``col*col`` ⟹ None). powdr emits timestamp
    gaps both as ``a + (-1)*b`` and as ``a - (b + c)``, so ``-`` must be parsed.
    """
    if isinstance(e, int):
        return ({}, to_signed(e))
    if isinstance(e, str):
        return ({e: 1}, 0)
    if isinstance(e, list) and len(e) == 2 and e[0] == "-":     # unary minus
        inner = linterms(e[1])
        if inner is None:
            return None
        return ({k: -v for k, v in inner[0].items()}, -inner[1])
    if isinstance(e, list) and len(e) == 3:
        a, op, b = e
        la, lb = linterms(a), linterms(b)
        if la is None or lb is None:
            return None
        if op in ("+", "-"):
            s = 1 if op == "+" else -1
            d = dict(la[0])
            for k, v in lb[0].items():
                d[k] = d.get(k, 0) + s * v
            return (d, la[1] + s * lb[1])
        if op == "*":
            if not la[0]:
                s = la[1]
                return ({k: s * v for k, v in lb[0].items()}, s * lb[1])
            if not lb[0]:
                s = lb[1]
                return ({k: s * v for k, v in la[0].items()}, s * la[1])
            return None
        return None
    return None


def deduce(dump: dict) -> tuple[set[tuple[str, str]], dict[str, tuple[str, bool, int]], set[str]]:
    """Apply R0/R1/R2. Returns ``(edges, recv_bound, nonneg)``.

    - ``edges``: set of ``(a, b)`` from_state columns, ``a`` strictly before ``b`` (R1).
    - ``recv_bound``: ``prev_ts col -> (from_state col, strict?, const)`` (R2).
    - ``nonneg``: range-checked ``>= 0`` columns (R0).
    """
    cons = dump["constraints"]
    bis = dump["bus_interactions"]
    nonneg: set[str] = set()
    for b in bis:
        if b.get("id") in (3, 6, 7):
            for a in b["args"]:
                names(a, nonneg)
    nonneg = {c for c in nonneg if isinstance(c, str)}
    nonneg |= {c for con in cons for c in names(con) if "lower_decomp" in c}

    edges: set[tuple[str, str]] = set()
    recv_bound: dict[str, tuple[str, bool, int]] = {}
    for con in cons:
        lt = linterms(con)
        if lt is None:
            continue
        coeffs = {k: v for k, v in lt[0].items() if v != 0}
        const = lt[1]
        tsv = [k for k in coeffs if is_ts(k)]
        nonts = [k for k in coeffs if not is_ts(k)]
        if any(k not in nonneg for k in nonts):
            continue
        fs = [k for k in tsv if is_fs(k)]
        pv = [k for k in tsv if is_prev(k)]
        limb_coeffs = {k: coeffs[k] for k in nonts}
        # R1: a pure pair of from_state columns
        if len(tsv) == 2 and len(fs) == 2 and not nonts:
            (a, ca), (b, cb) = [(k, coeffs[k]) for k in fs]
            if {ca, cb} == {1, -1}:
                pos = a if ca == 1 else b
                neg = b if ca == 1 else a
                gap = -const
                if gap > 0:
                    edges.add((neg, pos))
                elif gap < 0:
                    edges.add((pos, neg))
        # R2: one from_state, one prev_ts, any other vars are nonneg limbs
        if len(fs) == 1 and len(pv) == 1:
            f, pv0 = fs[0], pv[0]
            if coeffs[f] == 1 and coeffs[pv0] == -1:
                if (not limb_coeffs) or all(v < 0 for v in limb_coeffs.values()):
                    if pv0 not in recv_bound:
                        recv_bound[pv0] = (f, const <= -1, const)
    return edges, recv_bound, nonneg


def _all_cols(cons: list) -> set[str]:
    s: set[str] = set()
    for c in cons:
        names(c, s)
    return s


def _chain(nodes: list[str], edges: set[tuple[str, str]]) -> list[str] | None:
    """Return a linear order if ``edges`` define a total chain over ``nodes``, else None."""
    succ: dict[str, set[str]] = collections.defaultdict(set)
    indeg: dict[str, int] = collections.Counter()
    nodeset = set(nodes)
    for a, b in edges:
        if a in nodeset and b in nodeset and b not in succ[a]:
            succ[a].add(b)
            indeg[b] += 1
    indeg = dict(indeg)
    avail = [n for n in nodes if indeg.get(n, 0) == 0]
    order: list[str] = []
    while avail:
        avail.sort()
        n = avail.pop(0)
        order.append(n)
        for m in succ[n]:
            indeg[m] = indeg.get(m, 0) - 1
            if indeg[m] == 0:
                avail.append(m)
    return order if len(order) == len(nodes) else None


def total_order(dump: dict, edges: set[tuple[str, str]]) -> list[str]:
    """Linear order of from_state columns if the edges chain them; else ``[]``."""
    fs_all = sorted({c for c in _all_cols(dump["constraints"]) if is_fs(c)})
    return _chain(fs_all, edges) or []


def intra_offset(arg: Any) -> int:
    """The intra-instruction offset constant in a send ts expr ``from_state_K + off``."""
    off = 0
    if isinstance(arg, list) and len(arg) == 3 and arg[1] == "+":
        for side in (arg[0], arg[2]):
            if isinstance(side, int):
                off += to_signed(side)
    return off


def _r1_gaps(dump: dict) -> tuple[set[tuple[str, str]], dict[tuple[str, str], int]]:
    """R1 edges plus the concrete gap of each (``pos = neg + gap``)."""
    edges: set[tuple[str, str]] = set()
    gaps: dict[tuple[str, str], int] = {}
    for con in dump["constraints"]:
        lt = linterms(con)
        if lt is None:
            continue
        coeffs = {k: v for k, v in lt[0].items() if v != 0}
        const = lt[1]
        tsv = [k for k in coeffs if is_ts(k)]
        nonts = [k for k in coeffs if not is_ts(k)]
        fs = [k for k in tsv if is_fs(k)]
        if len(tsv) == 2 and len(fs) == 2 and not nonts:
            (a, ca), (b, cb) = [(k, coeffs[k]) for k in fs]
            if {ca, cb} == {1, -1}:
                pos = a if ca == 1 else b
                neg = b if ca == 1 else a
                gap = -const
                if gap > 0:
                    edges.add((neg, pos))
                    gaps[(neg, pos)] = gap
    return edges, gaps


def send_offsets(dump: dict) -> dict[str, int | None]:
    """Map each from_state column to its offset from the chain base ``T``.

    Accumulates the exact chain gaps along the total order; a column whose gap to
    its predecessor isn't an exact constant gets ``None`` (offset unknown). With
    these, a send at ``from_state_K + off`` is ``T + (send_offsets[K] + off)``.
    """
    edges, gaps = _r1_gaps(dump)
    chain = total_order(dump, edges)
    off: dict[str, int | None] = {}
    for i, col in enumerate(chain):
        if i == 0:
            off[col] = 0
            continue
        g = gaps.get((chain[i - 1], col))
        prev = off[chain[i - 1]]
        off[col] = (prev + g) if (g is not None and prev is not None) else None
    return off
