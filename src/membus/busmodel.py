"""Typed view of the bus tables — the only place that knows arg layouts.

Bus IDs (openvm/powdr conventions, cross-checked against the ``bus_map`` when
one is present):

- ``MEMORY`` (1): args = ``[address_space, pointer, b0, b1, b2, b3, timestamp]``
  (exactly 7). Send = write (mult +1), recv = read (mult −1).
- ``VAR_RANGE`` (3): args = ``[value, bits]`` — asserts the field residue of
  ``value`` lies in ``[0, 2^bits)``.
- ``BITWISE`` (6): args ``[x, y, z, op]`` — x and y are bytes.
- ``TUPLE_RANGE`` (7): per-element range check; carries no per-column width in
  its args, so it certifies nonnegativity only.

Everything else in membus consumes bus rows through :class:`MemRow` /
:func:`range_bus_rows`, never through raw ``b["args"][i]`` indexing.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Iterator

from src.lens.loader import machine_of
from src.lens.normalize import to_signed

MEMORY = 1
VAR_RANGE = 3
BITWISE = 6
TUPLE_RANGE = 7
RANGE_BUS_IDS = (VAR_RANGE, BITWISE, TUPLE_RANGE)

MEM_ARITY = 7


@dataclass(frozen=True)
class MemRow:
    """One memory-bus interaction, with its per-file membus ordinal."""

    ordinal: int      # index among the file's memory interactions (robust id)
    mult: Any         # multiplicity expression (raw dump form)
    args: tuple       # exactly MEM_ARITY entries

    @property
    def addr_space_expr(self) -> Any:
        return self.args[0]

    @property
    def addr_space(self) -> int | None:
        """The address space if constant, else None (symbolic AS)."""
        return to_signed(self.args[0]) if isinstance(self.args[0], int) else None

    @property
    def ptr(self) -> Any:
        return self.args[1]

    @property
    def data(self) -> tuple:
        return self.args[2:6]

    @property
    def ts(self) -> Any:
        return self.args[6]


def memory_rows(data: Any, mem_id: int = MEMORY) -> list[MemRow]:
    """All memory interactions in file order, arity-checked.

    Raises ``ValueError`` on a malformed row — a memory interaction with the
    wrong arity has no defined key/data/timestamp and nothing downstream can
    reason about it.
    """
    machine = machine_of(data)
    rows: list[MemRow] = []
    for b in machine.get("bus_interactions", []):
        if b.get("id") != mem_id:
            continue
        args = b.get("args", [])
        if len(args) != MEM_ARITY:
            raise ValueError(
                f"memory interaction #{len(rows)} has {len(args)} args, "
                f"expected {MEM_ARITY} (address_space, pointer, b0..b3, timestamp)")
        rows.append(MemRow(len(rows), b.get("mult"), tuple(args)))
    return rows


def range_bus_rows(data: Any) -> Iterator[tuple[int, int, list, Any]]:
    """Yield ``(bus_ordinal, bus_id, args, mult)`` for every range-check bus row.

    ``bus_ordinal`` is the row's index in the full ``bus_interactions`` list —
    the reference certificates use to point back at source material. ``mult`` is
    the interaction's multiplicity: a range check constrains its args only when
    sent (``mult != 0``), so a disabled row bounds nothing.
    """
    machine = machine_of(data)
    for i, b in enumerate(machine.get("bus_interactions", [])):
        if b.get("id") in RANGE_BUS_IDS:
            yield i, b["id"], b.get("args", []), b.get("mult")


def row_key(row: MemRow) -> str:
    """Syntactic identity of a row (mult + args), for duplicate / diff checks."""
    return json.dumps([row.mult, list(row.args)], sort_keys=True)


def find_duplicates(rows: list[MemRow]) -> list[tuple[str, int]]:
    """Identical interactions (same mult + args), as ``(key, count>1)``.

    A sound memory bus has none: each access has a unique timestamp, so two
    field-identical interactions would make the offline pairing ill-defined.
    """
    counts: dict[str, int] = {}
    for r in rows:
        k = row_key(r)
        counts[k] = counts.get(k, 0) + 1
    return [(k, c) for k, c in counts.items() if c > 1]


def removed_rows(pre: list[MemRow], post: list[MemRow]) -> list[MemRow]:
    """Rows present in ``pre`` but not in ``post`` (syntactic multiset diff)."""
    post_counts: dict[str, int] = {}
    for r in post:
        k = row_key(r)
        post_counts[k] = post_counts.get(k, 0) + 1
    removed = []
    for r in pre:
        k = row_key(r)
        if post_counts.get(k, 0) > 0:
            post_counts[k] -= 1
        else:
            removed.append(r)
    return removed


def symbolic_as_ordinals(rows: list[MemRow]) -> list[int]:
    """Ordinals whose address space is not a constant int (pre-`solver` flag
    muxes) — such a row could belong to ANY address space and must not be
    silently dropped by an ``addr_space == N`` filter."""
    return [r.ordinal for r in rows if r.addr_space is None]


def require_explicit_address_spaces(rows: list[MemRow], subject: str) -> None:
    """Shared precondition for solve / align: raise unless in solved AS form."""
    syms = symbolic_as_ordinals(rows)
    if syms:
        raise ValueError(
            f"{subject}: {len(syms)} memory interaction(s) have a symbolic address "
            f"space (e.g. #{syms[0]}) — requires solved AS form (all address spaces "
            f"explicit)")


def bus_ordinal_of_mem(data: Any, mem_id: int = MEMORY) -> dict[int, int]:
    """Map membus ordinal -> index in the full bus_interactions list."""
    machine = machine_of(data)
    out: dict[int, int] = {}
    n = 0
    for i, b in enumerate(machine.get("bus_interactions", [])):
        if b.get("id") == mem_id:
            out[n] = i
            n += 1
    return out
