"""Structural statistics over a dump's machine data.

Constraints, bus ``args`` and ``mult`` are expression trees of the form
``[lhs, op, rhs]`` (operators ``+ - *``), with int constants and
``"name@idx"`` column refs as leaves. ``mult`` may also be a bare int
(``1`` send, ``prime-1``/``-1`` recv) or a bare column string.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from statistics import mean
from typing import Any

FIELD_PRIME = 2013265921  # BabyBear
NEG_ONE = FIELD_PRIME - 1
_OPS = {"+", "-", "*"}


@dataclass
class ExprInfo:
    """Aggregates from walking one expression tree."""

    nodes: int
    depth: int
    degree: int
    columns: set[str]
    ops: Counter


def analyze_expr(node: Any) -> ExprInfo:
    """Recursively measure an expression tree.

    ``degree`` is the polynomial degree: constant=0, column=1, ``+``/``-``
    take the max of operands, ``*`` sums them. This is the metric passes like
    ``low_degree_bus`` target.
    """
    if isinstance(node, bool):  # bool is an int subclass — handle first
        return ExprInfo(1, 1, 0, set(), Counter())
    if isinstance(node, (int, float)):
        return ExprInfo(1, 1, 0, set(), Counter())
    if isinstance(node, str):
        return ExprInfo(1, 1, 1, {node}, Counter())
    if isinstance(node, list):
        if not node:
            return ExprInfo(1, 1, 0, set(), Counter())
        # Two encodings: prefix/unary ``[op, operand, ...]`` (e.g. ['-', e]
        # negation) and infix ``[operand, op, operand, ...]``.
        if isinstance(node[0], str) and node[0] in _OPS:
            op = node[0]
            operands = [analyze_expr(x) for x in node[1:]]
            op_tokens = [op]
        else:
            operands = [analyze_expr(node[i]) for i in range(0, len(node), 2)]
            op_tokens = [node[i] for i in range(1, len(node), 2)]
        if not operands:
            return ExprInfo(1, 1, 0, set(), Counter())
        nodes = sum(o.nodes for o in operands) + len(op_tokens)
        depth = 1 + max(o.depth for o in operands)
        columns: set[str] = set().union(*(o.columns for o in operands))
        ops = Counter(t for t in op_tokens if t in _OPS)
        for o in operands:
            ops += o.ops
        degree = operands[0].degree
        for tok, o in zip(op_tokens, operands[1:]):
            degree = degree + o.degree if tok == "*" else max(degree, o.degree)
        return ExprInfo(nodes, depth, degree, columns, ops)
    if isinstance(node, dict):  # e.g. derived-column form wrapper
        children = [analyze_expr(v) for v in node.values()]
        if not children:
            return ExprInfo(1, 1, 0, set(), Counter())
        return ExprInfo(
            1 + sum(c.nodes for c in children),
            1 + max(c.depth for c in children),
            max(c.degree for c in children),
            set().union(*(c.columns for c in children)),
            sum((c.ops for c in children), Counter()),
        )
    return ExprInfo(1, 1, 0, set(), Counter())


def mult_kind(mult: Any) -> str:
    """Classify a bus multiplicity into send / recv / sym / other."""
    if isinstance(mult, bool):
        return "other"
    if isinstance(mult, int):
        if mult == 1:
            return "send"
        if mult in (NEG_ONE, -1):
            return "recv"
        return "other"
    return "sym"  # symbolic: column string or expression tree


@dataclass
class Spread:
    """min / mean / max summary of a numeric series (zeros when empty)."""

    min: int = 0
    mean: float = 0.0
    max: int = 0

    @classmethod
    def of(cls, values: list[int]) -> "Spread":
        if not values:
            return cls()
        return cls(min(values), round(mean(values), 2), max(values))

    def as_dict(self) -> dict[str, float]:
        return {"min": self.min, "mean": self.mean, "max": self.max}


@dataclass
class BusRow:
    """Per-bus-id interaction summary."""

    id: str
    label: str
    count: int = 0
    send: int = 0
    recv: int = 0
    sym: int = 0
    other: int = 0
    args_nodes: int = 0

    def as_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "label": self.label,
            "count": self.count,
            "send": self.send,
            "recv": self.recv,
            "sym": self.sym,
            "other": self.other,
            "args_nodes": self.args_nodes,
        }


@dataclass
class DumpStats:
    """All statistics computed for a single dump."""

    fmt: str = "unknown"
    n_constraints: int = 0
    n_bus_interactions: int = 0
    n_derived_columns: int = 0
    distinct_columns: int = 0
    degree: Spread = field(default_factory=Spread)
    degree_hist: Counter = field(default_factory=Counter)
    nodes: Spread = field(default_factory=Spread)
    depth: Spread = field(default_factory=Spread)
    op_hist: Counter = field(default_factory=Counter)
    buses: list[BusRow] = field(default_factory=list)
    derived_forms: Counter = field(default_factory=Counter)
    # base-dump-only extras (None when absent)
    n_blocks: int | None = None
    n_instructions: int | None = None
    submachine_polys: list[int] | None = None

    @classmethod
    def from_data(
        cls, data: dict[str, Any], labels: dict[str, str]
    ) -> "DumpStats":
        from .loader import detect_format, machine_of

        machine = machine_of(data)
        s = cls()
        s.fmt = detect_format(data)

        degrees, nodes, depths = [], [], []
        all_cols: set[str] = set()
        for c in machine.get("constraints", []):
            info = analyze_expr(c)
            degrees.append(info.degree)
            nodes.append(info.nodes)
            depths.append(info.depth)
            all_cols |= info.columns
            s.op_hist += info.ops
        s.n_constraints = len(degrees)
        s.degree = Spread.of(degrees)
        s.degree_hist = Counter(degrees)
        s.nodes = Spread.of(nodes)
        s.depth = Spread.of(depths)

        rows: dict[str, BusRow] = {}
        bis = machine.get("bus_interactions", [])
        s.n_bus_interactions = len(bis)
        for bi in bis:
            bid = str(bi.get("id"))
            row = rows.setdefault(bid, BusRow(bid, labels.get(bid, "?")))
            row.count += 1
            kind = mult_kind(bi.get("mult"))
            setattr(row, kind, getattr(row, kind) + 1)
            for arg in bi.get("args", []):
                row.args_nodes += analyze_expr(arg).nodes
        s.buses = sorted(rows.values(), key=lambda r: (-r.count, r.id))

        derived = machine.get("derived_columns", [])
        s.n_derived_columns = len(derived)
        for d in derived:
            if isinstance(d, list) and len(d) >= 3 and isinstance(d[2], dict):
                all_cols |= analyze_expr(d[2]).columns
                s.derived_forms[next(iter(d[2]))] += 1
            else:
                s.derived_forms["?"] += 1

        s.distinct_columns = len(all_cols)

        # base-dump extras
        if "block" in data:
            blocks = data["block"].get("blocks", [])
            s.n_blocks = len(blocks)
            s.n_instructions = sum(len(b.get("instructions", [])) for b in blocks)
        if "subs" in data:
            s.submachine_polys = [len(g) for g in data["subs"]]

        return s

    def as_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "format": self.fmt,
            "n_constraints": self.n_constraints,
            "n_bus_interactions": self.n_bus_interactions,
            "n_derived_columns": self.n_derived_columns,
            "distinct_columns": self.distinct_columns,
            "degree": self.degree.as_dict(),
            "degree_hist": {str(k): v for k, v in sorted(self.degree_hist.items())},
            "nodes": self.nodes.as_dict(),
            "depth": self.depth.as_dict(),
            "op_hist": dict(sorted(self.op_hist.items())),
            "buses": [r.as_dict() for r in self.buses],
            "derived_forms": dict(sorted(self.derived_forms.items())),
        }
        if self.n_blocks is not None:
            d["n_blocks"] = self.n_blocks
            d["n_instructions"] = self.n_instructions
        if self.submachine_polys is not None:
            d["submachine_polys"] = self.submachine_polys
        return d


@dataclass
class DumpDiff:
    """Deltas between two DumpStats (A -> B)."""

    a: DumpStats
    b: DumpStats

    def scalar_deltas(self) -> dict[str, tuple[int, int]]:
        """Map metric name -> (A, B) for the scalar counts."""
        keys = [
            "n_constraints",
            "n_bus_interactions",
            "n_derived_columns",
            "distinct_columns",
        ]
        return {k: (getattr(self.a, k), getattr(self.b, k)) for k in keys}

    def bus_deltas(self) -> list[tuple[str, str, int, int]]:
        """(id, label, A_count, B_count) over the union of bus ids."""
        ra = {r.id: r for r in self.a.buses}
        rb = {r.id: r for r in self.b.buses}
        ids = sorted(
            set(ra) | set(rb),
            key=lambda i: (-(ra.get(i, BusRow(i, "")).count + rb.get(i, BusRow(i, "")).count), i),
        )
        out = []
        for i in ids:
            label = (ra.get(i) or rb.get(i)).label
            out.append((i, label, ra.get(i, BusRow(i, "")).count, rb.get(i, BusRow(i, "")).count))
        return out

    def op_deltas(self) -> dict[str, tuple[int, int]]:
        keys = sorted(set(self.a.op_hist) | set(self.b.op_hist))
        return {k: (self.a.op_hist.get(k, 0), self.b.op_hist.get(k, 0)) for k in keys}

    def as_dict(self) -> dict[str, Any]:
        return {
            "format": {"a": self.a.fmt, "b": self.b.fmt},
            "scalars": {
                k: {"a": va, "b": vb, "delta": vb - va}
                for k, (va, vb) in self.scalar_deltas().items()
            },
            "buses": [
                {"id": i, "label": lbl, "a": ca, "b": cb, "delta": cb - ca}
                for i, lbl, ca, cb in self.bus_deltas()
            ],
            "op_hist": {
                k: {"a": va, "b": vb, "delta": vb - va}
                for k, (va, vb) in self.op_deltas().items()
            },
            "degree_mean": {
                "a": self.a.degree.mean,
                "b": self.b.degree.mean,
                "delta": round(self.b.degree.mean - self.a.degree.mean, 2),
            },
        }
