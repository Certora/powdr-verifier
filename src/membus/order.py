"""Timestamp order deduction over Gap facts: the send chain and virtual time.

The memory-bus pairing is fixed by (key, timestamp), and cross-interaction
reasoning only ever needs the timestamps *relative to one base*: the *virtual
time* of a send is its offset from the first send's from_state clock. This
module derives that from :class:`~.facts.Gap` facts alone:

- :func:`total_send_order` — the from_state columns in a **verified** total
  order. Unlike a plain topological sort, this requires exactly one available
  node at every step: a partial order is reported as ``None``, never silently
  linearized by a tie-break (review finding 2).
- :func:`send_offsets` — each from_state column's exact integer offset from
  the chain base, accumulated along *direct* Gap facts between consecutive
  chain elements; ``None`` where no direct gap pins the offset.
"""
from __future__ import annotations

import collections
from typing import Any

from . import naming
from .facts import Gap
from .linform import linform, names
from .rules import Analysis


def ts_col(arg: Any) -> str | None:
    """The single timestamp-domain column in a timestamp arg, or None."""
    ts = [c for c in names(arg) if naming.is_ts(c)]
    return ts[0] if len(ts) == 1 else None


def intra_offset(arg: Any) -> int:
    """The constant offset in a send timestamp arg ``fs_col + off``.

    Exact parse: the arg must be affine in a single column with coefficient 1
    (the shape powdr emits); anything else contributes offset 0 — callers that
    need the offset to be trusted must have checked the shape via `ts_col`.
    """
    lf = linform(arg)
    if lf is not None and len(lf.coeffs) == 1 and lf.coeffs[0][1] == 1:
        return lf.const
    return 0


def access_index(col: str) -> int | None:
    """Instruction index K from a ``..._<K>@<n>`` timestamp column name
    (display only — deduction never uses it)."""
    import re
    m = re.search(r"_(\d+)@\d+$", col)
    return int(m.group(1)) if m else None


def all_fs_columns(an: Analysis) -> list[str]:
    """All from_state columns in the dump — constraints AND bus args (after
    `inlining` they survive only inside bus args)."""
    s: set[str] = set()
    for c in an.machine.get("constraints", []):
        names(c, s)
    for b in an.machine.get("bus_interactions", []):
        names(b.get("args", []), s)
    return sorted(c for c in s if naming.is_fs(c))


def total_send_order(an: Analysis) -> list[str] | None:
    """The verified total order of from_state columns, or None.

    The Gap facts must force a *unique* linearization: at every step of the
    topological traversal exactly one column may be available. Ambiguity means
    the constraints do not order the sends and no order is invented.
    """
    nodes = all_fs_columns(an)
    nodeset = set(nodes)
    succ: dict[str, set[str]] = collections.defaultdict(set)
    indeg: dict[str, int] = dict.fromkeys(nodes, 0)
    for g in an.gaps:
        if g.earlier in nodeset and g.later in nodeset and g.later not in succ[g.earlier]:
            succ[g.earlier].add(g.later)
            indeg[g.later] += 1
    avail = [n for n in nodes if indeg[n] == 0]
    order: list[str] = []
    while avail:
        if len(avail) != 1:
            return None                      # partial order — refuse to linearize
        n = avail.pop()
        order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                avail.append(m)
    return order if len(order) == len(nodes) else None    # cycle ⟹ None


def send_offsets(an: Analysis) -> dict[str, int | None]:
    """from_state column → exact offset from the chain base (or None).

    Offsets accumulate along direct Gap facts between consecutive elements of
    the total order; a consecutive pair ordered only transitively has no exact
    gap, so the later column (and everything after it) gets None.
    """
    chain = total_send_order(an)
    if chain is None:
        return dict.fromkeys(all_fs_columns(an), None)
    direct: dict[tuple[str, str], int] = {}
    for g in an.gaps:
        direct[(g.earlier, g.later)] = g.gap
    off: dict[str, int | None] = {}
    for i, col in enumerate(chain):
        if i == 0:
            off[col] = 0
            continue
        g = direct.get((chain[i - 1], col))
        prev = off[chain[i - 1]]
        off[col] = (prev + g) if (g is not None and prev is not None) else None
    return off


def gap_between(an: Analysis, earlier: str, later: str) -> Gap | None:
    """The direct Gap fact between two columns, if any (for certificates)."""
    for g in an.gaps:
        if g.earlier == earlier and g.later == later:
            return g
    return None
