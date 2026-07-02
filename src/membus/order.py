"""Timestamp offsets over Gap facts: virtual time for every clock column.

The memory-bus pairing is fixed by (key, timestamp), and cross-interaction
reasoning only ever needs the timestamps *relative to one base*. Everything
here is positional — the clock web comes from `rules.Analysis.ts_domain`
(membus timestamp slots + gap closure), never from column names.

The clock web is a graph whose edges are Gap facts (``later = earlier +
gap``). Offsets are propagated per connected component and **conflict-checked**
(two gap paths disagreeing on a column's offset poison the whole component —
no offset is invented). Each component is normalized so its minimum offset is
0. There is no "total chain" requirement: what `solve`/`align` need is that
every *send clock* has a resolved offset in one common component — enforced
by :func:`send_offsets` — and per-cell distinctness of send times, which
`solve` checks explicitly.
"""
from __future__ import annotations

import collections
from typing import Any

from .facts import Gap
from .linform import linform
from .rules import Analysis


def ts_col(arg: Any) -> str | None:
    """The column of a timestamp-slot arg ``col + const`` (coefficient 1),
    or None. Positional: whatever single column sits in the slot IS the
    timestamp; anything more complex is unresolved."""
    return Analysis._slot_col(arg)


def intra_offset(arg: Any) -> int:
    """The constant offset in a send timestamp arg ``col + off``."""
    lf = linform(arg)
    if lf is not None and len(lf.coeffs) == 1 and lf.coeffs[0][1] == 1:
        return lf.const
    return 0


def clock_offsets(an: Analysis) -> tuple[dict[str, int | None], dict[str, int]]:
    """``(offsets, component)`` over the clock web.

    Offsets are exact integers relative to the column's connected component
    (normalized: component minimum = 0), or None when the component contains
    conflicting gap paths. ``component`` maps each clock column to a
    component id."""
    adj: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    for g in an.gaps:
        adj[g.earlier].append((g.later, g.gap))     # later = earlier + gap
        adj[g.later].append((g.earlier, -g.gap))
    offsets: dict[str, int | None] = {}
    component: dict[str, int] = {}
    comp = 0
    for root in sorted(an.clock_cols):
        if root in component:
            continue
        # BFS this component
        rel: dict[str, int] = {root: 0}
        queue = [root]
        ok = True
        while queue:
            cur = queue.pop()
            for nxt, d in adj[cur]:
                v = rel[cur] + d
                if nxt in rel:
                    if rel[nxt] != v:
                        ok = False                   # conflicting paths
                else:
                    rel[nxt] = v
                    queue.append(nxt)
        base = min(rel.values())
        for col, v in rel.items():
            component[col] = comp
            offsets[col] = (v - base) if ok else None
        comp += 1
    return offsets, component


def send_offsets(an: Analysis) -> dict[str, int | None]:
    """Clock column → offset from the common base, or None.

    Resolved only when every *send clock* (the slot column of a resolved
    send interaction) lives in one conflict-free component; clock columns
    outside that component get None. Empty/unresolvable ⟹ all None."""
    offsets, component = clock_offsets(an)
    send_comps: set[int] = set()
    for row in an.mem:
        k = an.kinds.get(row.ordinal)
        if k is None or k.kind != "send":
            continue
        col = Analysis._slot_col(row.ts)
        if col is None or col not in component or offsets.get(col) is None:
            return dict.fromkeys(an.clock_cols, None)
        send_comps.add(component[col])
    if len(send_comps) != 1:
        return dict.fromkeys(an.clock_cols, None)
    main = send_comps.pop()
    return {col: (offsets[col] if component.get(col) == main else None)
            for col in an.clock_cols}


def send_order(an: Analysis) -> list[str] | None:
    """Clock columns with resolved offsets, sorted by offset (display /
    preconditions), or None when nothing resolves."""
    soff = send_offsets(an)
    resolved = {c: v for c, v in soff.items() if v is not None}
    if not resolved:
        return None
    return sorted(resolved, key=lambda c: (resolved[c], c))


def gap_between(an: Analysis, earlier: str, later: str) -> Gap | None:
    """The direct Gap fact between two columns, if any (for certificates)."""
    for g in an.gaps:
        if g.earlier == earlier and g.later == later:
            return g
    return None
