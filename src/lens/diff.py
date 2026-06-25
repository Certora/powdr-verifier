"""Constraint-level diff between two same-representation dumps.

Reports constraints removed / added / changed, plus columns added/removed
(annotated with their substitution / derived-column definitions).

Restricted to a single representation: powdr flips between the ``machine``
(AlgebraicExpression) and ``constraints`` (GroupedExpression) encodings between
passes, and that flip is usually coincidental (no real optimization), so a
cross-encoding diff is mostly noise. ``build_diff`` refuses M-vs-C.

Canonicalization is light/structural — signed constants + flatten/sort of
commutative ``+``/``*`` with identity folding, NO polynomial distribution.
Within one representation that is enough (verified: C-C pairs are pure
add/remove); the lone exception is the ``loop_iteration`` M-M pair, which
distributes and surfaces as "changed".
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Any

from .loader import detect_format, machine_of
from .metrics import analyze_expr
from .normalize import to_signed

_DIFFABLE = {"machine", "constraints"}


class DiffError(Exception):
    """Raised when two dumps cannot be constraint-diffed (e.g. M vs C)."""


def canon_constraint(node: Any) -> Any:
    """Hashable canonical form: signed constants, flattened/sorted +/*.

    Does NOT distribute products. Within one representation, structurally equal
    constraints (modulo reassociation, commutativity, ``0+``/``*1`` and the
    signed-vs-residue constant encoding) map to the same key.
    """
    if isinstance(node, bool):
        return ("c", 0)
    if isinstance(node, int):
        return ("c", to_signed(node))
    if isinstance(node, str):
        return ("v", node)
    if isinstance(node, list) and node:
        if node[0] == "-" and len(node) == 2:  # unary minus
            return _mul([("c", -1), canon_constraint(node[1])])
        acc = canon_constraint(node[0])
        for i in range(1, len(node), 2):
            op, rhs = node[i], canon_constraint(node[i + 1])
            if op == "+":
                acc = _add([acc, rhs])
            elif op == "-":
                acc = _add([acc, _mul([("c", -1), rhs])])
            elif op == "*":
                acc = _mul([acc, rhs])
        return acc
    return ("c", 0)


def _add(terms: list) -> Any:
    flat: list = []
    const = 0
    for t in terms:
        if t[0] == "+":
            flat.extend(t[1])
        elif t[0] == "c":
            const += t[1]
        else:
            flat.append(t)
    const = to_signed(const)
    if const:
        flat.append(("c", const))
    flat = [t for t in flat if t != ("c", 0)]
    if not flat:
        return ("c", 0)
    if len(flat) == 1:
        return flat[0]
    return ("+", tuple(sorted(flat, key=repr)))


def _mul(factors: list) -> Any:
    flat: list = []
    const = 1
    for f in factors:
        if f[0] == "*":
            flat.extend(f[1])
        elif f[0] == "c":
            const *= f[1]
        else:
            flat.append(f)
    const = to_signed(const)
    if const == 0:
        return ("c", 0)
    if const != 1:
        flat.append(("c", const))
    if not flat:
        return ("c", 1)
    if len(flat) == 1:
        return flat[0]
    return ("*", tuple(sorted(flat, key=repr)))


def _cols(c: Any) -> set[str]:
    return analyze_expr(c).columns


def _jaccard(s: set, t: set) -> float:
    if not s and not t:
        return 1.0
    u = s | t
    return len(s & t) / len(u) if u else 1.0


@dataclass
class ConstraintDiff:
    """Result of diffing two same-representation dumps."""

    fmt: str
    removed: list = field(default_factory=list)         # original constraints
    added: list = field(default_factory=list)
    changed: list = field(default_factory=list)         # (before, after) pairs
    cols_added: list = field(default_factory=list)       # (name, def|None)
    cols_removed: list = field(default_factory=list)      # (name, def|None)


def build_diff(
    a_data: Any,
    b_data: Any,
    subs: list | None = None,
    match_threshold: float = 0.5,
) -> ConstraintDiff:
    """Diff constraints of two dumps; raise DiffError unless same representation.

    ``subs`` is the block's ``_substitutions.json`` list (``[var, def]``), used
    to annotate removed columns.
    """
    fa, fb = detect_format(a_data), detect_format(b_data)
    if fa not in _DIFFABLE or fb not in _DIFFABLE:
        raise DiffError(f"not constraint dumps (A={fa}, B={fb})")
    if fa != fb:
        raise DiffError(
            f"cannot diff across representations: A is {fa}, B is {fb}. "
            f"The M/C flip is just an encoding change — diff two {fa} steps "
            f"or two {fb} steps.")

    ma, mb = machine_of(a_data), machine_of(b_data)
    ca, cb = ma.get("constraints", []), mb.get("constraints", [])

    # multiset diff on canonical keys, keeping one original per key for display
    ka: Counter = Counter()
    kb: Counter = Counter()
    origa: dict = {}
    origb: dict = {}
    for c in ca:
        k = canon_constraint(c)
        ka[k] += 1
        origa.setdefault(k, c)
    for c in cb:
        k = canon_constraint(c)
        kb[k] += 1
        origb.setdefault(k, c)

    removed = [origa[k] for k, n in (ka - kb).items() for _ in range(n)]
    added = [origb[k] for k, n in (kb - ka).items() for _ in range(n)]

    # greedy similarity matching of residuals -> "changed"
    rcols = [_cols(r) for r in removed]
    acols = [_cols(a) for a in added]
    cand = []
    for i in range(len(removed)):
        for j in range(len(added)):
            s = _jaccard(rcols[i], acols[j])
            if s >= match_threshold:
                cand.append((s, i, j))
    cand.sort(reverse=True, key=lambda x: x[0])
    used_r: set = set()
    used_a: set = set()
    changed = []
    for _, i, j in cand:
        if i in used_r or j in used_a:
            continue
        used_r.add(i)
        used_a.add(j)
        changed.append((removed[i], added[j]))
    removed = [r for i, r in enumerate(removed) if i not in used_r]
    added = [a for j, a in enumerate(added) if j not in used_a]

    # columns added/removed, annotated with defs
    cols_a: set[str] = set().union(*(_cols(c) for c in ca)) if ca else set()
    cols_b: set[str] = set().union(*(_cols(c) for c in cb)) if cb else set()
    subs_map = {v: d for v, d in (subs or [])}
    derived_map = {
        d[1]: d[2] for d in mb.get("derived_columns", [])
        if isinstance(d, list) and len(d) >= 3
    }
    cols_added = [(n, derived_map.get(n)) for n in sorted(cols_b - cols_a)]
    cols_removed = [(n, subs_map.get(n)) for n in sorted(cols_a - cols_b)]

    return ConstraintDiff(
        fmt=fa,
        removed=removed,
        added=added,
        changed=changed,
        cols_added=cols_added,
        cols_removed=cols_removed,
    )
