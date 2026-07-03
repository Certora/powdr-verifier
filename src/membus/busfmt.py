"""busat ``.bus`` text emission: atoms, DEFS lifting, name sanitizing.

The busat ``.bus`` format used by `extract` treats each MEM field as a single
atom (a `z3.Int(name)` or integer literal), so any compound field must be
lifted into a DEFS line. `Emitter` does that lifting (with common-subexpression
sharing). Reading bus rows lives in `busmodel`; this module only renders.
"""
from __future__ import annotations

from typing import Any

from src.lens.normalize import to_signed


def memory_bus_id(labels: dict[str, str]) -> int:
    """The bus id whose label is "Memory" (default 1 if unmapped)."""
    for k, v in labels.items():
        if v == "Memory":
            try:
                return int(k)
            except ValueError:
                pass
    return 1


def sanitize(name: str) -> str:
    """Turn a powdr column name into a valid Python identifier for busat.

    Column names look like ``reads_aux__0__base__prev_timestamp_3@115``; the only
    offending character is ``@``, mapped to ``_at_`` (stable, collision-free).
    """
    out = name.replace("@", "_at_")
    if not out.isidentifier():
        out = "".join(c if (c.isalnum() or c == "_") else "_" for c in out)
        if out and out[0].isdigit():
            out = "v_" + out
    return out


class Emitter:
    """Accumulates DEFS while translating dump exprs to busat atoms/expressions."""

    def __init__(self) -> None:
        self.defs: dict[str, str] = {}      # var -> expr string
        self._by_expr: dict[str, str] = {}  # expr string -> var (CSE)
        self._fresh = 0

    def fresh(self, hint: str = "t") -> str:
        self._fresh += 1
        return f"{hint}_{self._fresh}"

    def expr_str(self, e: Any) -> str:
        """Render a dump expr as a busat (python-ast) expression string."""
        if isinstance(e, bool):
            raise ValueError(f"unexpected bool expr: {e!r}")
        if isinstance(e, int):
            return str(to_signed(e))
        if isinstance(e, str):
            return sanitize(e)
        if isinstance(e, list) and len(e) == 2 and e[0] == "-":
            return f"(-{self.expr_str(e[1])})"
        if isinstance(e, list) and len(e) == 3:
            lhs, op, rhs = e
            if op not in ("+", "-", "*"):
                raise ValueError(f"unsupported op {op!r} in {e!r}")
            return f"({self.expr_str(lhs)} {op} {self.expr_str(rhs)})"
        raise ValueError(f"cannot render expr: {e!r}")

    def atom(self, e: Any, hint: str) -> str:
        """Return a busat MEM-field atom for ``e`` (int literal or identifier).

        A bare atom (int or column) is returned directly; a compound is lifted
        into a fresh DEFS var, sharing one var per distinct expression (CSE).
        """
        if isinstance(e, int):
            return str(to_signed(e))
        if isinstance(e, str):
            return sanitize(e)
        rendered = self.expr_str(e)
        if rendered in self._by_expr:
            return self._by_expr[rendered]
        var = self.fresh(hint)
        self.defs[var] = rendered
        self._by_expr[rendered] = var
        return var
