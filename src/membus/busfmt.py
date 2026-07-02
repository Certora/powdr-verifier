"""Low-level helpers: read memory-bus interactions, emit busat-format text.

The busat ``.bus`` format used by `extract` treats each MEM field as a single
atom (a `z3.Int(name)` or integer literal), so any compound field must be lifted
into a DEFS line. `Emitter` does that lifting (with common-subexpression sharing).
These helpers are ports of the validated prototypes in `busat/tools/dump_to_bus.py`.
"""
from __future__ import annotations

import json
from typing import Any

from src.lens.loader import machine_of
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


def memory_bis(data: Any, mem_id: int = 1) -> list[dict]:
    """All memory bus interactions (id == mem_id) in file order.

    Their index in this list is the per-file **membus ordinal**.
    """
    machine = machine_of(data)
    return [b for b in machine.get("bus_interactions", []) if b.get("id") == mem_id]


def _bi_key(bi: dict) -> str:
    return json.dumps([bi["id"], bi["mult"], bi["args"]], sort_keys=True)


def symbolic_as_ordinals(data: Any, mem_id: int = 1) -> list[int]:
    """Membus ordinals whose address space (args[0]) is NOT a constant int.

    "Solved AS form" = every memory interaction has an explicit constant address
    space. Before the `solver` pass resolves the instruction variant, an
    interaction's AS can be a flag-multiplex (symbolic) and could be any address
    space — so it must not be silently dropped by an ``as == N`` filter.
    """
    return [i for i, b in enumerate(memory_bis(data, mem_id))
            if not isinstance(b["args"][0], int)]


def require_explicit_address_spaces(data: Any, mem_id: int, subject: str) -> None:
    """Shared precondition for `solve` / `align`: raise unless in solved AS form."""
    syms = symbolic_as_ordinals(data, mem_id)
    if syms:
        raise ValueError(
            f"{subject}: {len(syms)} memory interaction(s) have a symbolic address "
            f"space (e.g. #{syms[0]}) — requires solved AS form (all address spaces "
            f"explicit)")


def find_duplicates(bis: list[dict]) -> list[tuple[str, int]]:
    """Identical interactions (same mult + args) in ``bis``, as ``(key, count)``.

    A memory bus must not contain a duplicated interaction: each access has a
    unique timestamp, so two interactions identical in every field (including
    timestamp) would make the offline-memory pairing ill-defined. Returns the
    groups whose count > 1 (empty ⟹ all interactions are distinct).
    """
    counts: dict[str, int] = {}
    for b in bis:
        k = _bi_key(b)
        counts[k] = counts.get(k, 0) + 1
    return [(k, c) for k, c in counts.items() if c > 1]


def removed_memory_bis(pre: Any, post: Any, mem_id: int = 1) -> list[dict]:
    """Memory interactions present in `pre` but removed in `post` (multiset diff).

    These are exactly the interactions a pass eliminated — the set whose internal
    balancing makes the removal sound.
    """
    rows = memory_bis(pre, mem_id)
    post_keys: dict[str, int] = {}
    for b in memory_bis(post, mem_id):
        k = _bi_key(b)
        post_keys[k] = post_keys.get(k, 0) + 1
    removed = []
    for b in rows:
        k = _bi_key(b)
        if post_keys.get(k, 0) > 0:
            post_keys[k] -= 1
        else:
            removed.append(b)
    return removed


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


def names_of(e: Any, acc: set[str] | None = None) -> set[str]:
    """Collect column names referenced in a dump expr."""
    if acc is None:
        acc = set()
    if isinstance(e, str):
        acc.add(e)
    elif isinstance(e, list):
        for x in e:
            names_of(x, acc)
    return acc


def flatten_sum(e: Any) -> list[Any]:
    """Flatten a top-level additive expression into a list of (signed) terms.

    powdr renders subtraction as ``+ (-1 * x)``, so ``+`` is the usual top-level
    operator; ``-`` is handled defensively by marker-negating the right operand.
    """
    if isinstance(e, list) and len(e) == 3 and e[1] in ("+", "-"):
        lhs, op, rhs = e
        terms = flatten_sum(lhs)
        if op == "-":
            terms += [["-", t] for t in flatten_sum(rhs)]
        else:
            terms += flatten_sum(rhs)
        return terms
    return [e]


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
