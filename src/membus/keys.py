"""Recover memory keys (the ``(address_space, pointer)`` of an interaction) and
classify an address space's alias structure.

A pointer is one of:
- a **constant** (a fixed address — register file / fixed slot);
- a symbolic **base + offset** — recovered from the limb-decomposition gadget,
  where the offset is a clean integer and the base identifies the register the
  address is computed from (``rs1`` directly, or a value loaded from memory);
- **unresolved** — symbolic but not in the recognized shape.

Whether an address space partitions cleanly into alias sets (no cross-set
aliasing) is decidable only when keys are pairwise distinguishable: all
constant, or all ``base+offset`` sharing one base (distinct offsets ⟹ distinct).
Otherwise — multiple bases, or unresolved keys — aliasing is *not* statically
known, and we flag it rather than assert disjointness.

Key recovery is ported from ``busat/tools/dump_to_bus_coi.py``.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from src.lens.normalize import to_signed

from .busfmt import Emitter, flatten_sum, names_of

# The low-limb address-decomposition constraint scales register/limb by this
# factor; offset = -const / SCALE. Calibrated to the keccak (2100224) dumps.
ADDR_SCALE = 30720

_LOW_LIMB_RE = re.compile(r"mem_ptr_limbs__0_\d+@\d+")
# Base register low byte in a low-limb constraint: <base>_data__0_<k>@<col>.
# E.g. rs1_data__0_0@3 (direct) or read_data__0_314@12875 (indirect). The base
# KEY is everything before the byte index, so addresses off the same register
# share a base.
_BASE_RE = re.compile(r"(.+)_data__0_(\d+)@\d+")


@dataclass(frozen=True)
class Const:
    """A constant (fixed) address."""
    value: int

    def __str__(self) -> str:
        return f"const {self.value}"


@dataclass(frozen=True)
class BaseOffset:
    """``base + offset`` — a symbolic address with a recovered constant offset."""
    base: str
    offset: int

    def __str__(self) -> str:
        return f"{self.base}+{self.offset}"


@dataclass(frozen=True)
class Unresolved:
    """A symbolic pointer not in the recognized base+offset shape."""
    expr: str

    def __str__(self) -> str:
        return f"unresolved({self.expr})"


Key = Const | BaseOffset | Unresolved


def _const_of(e: Any) -> int:
    """Sum of bare integer terms in an additive expression (signed)."""
    tot = 0
    for t in flatten_sum(e):
        if isinstance(t, int):
            tot += to_signed(t)
        elif isinstance(t, list) and len(t) == 2 and t[0] == "-" and isinstance(t[1], int):
            tot -= to_signed(t[1])
    return tot


def low_limb_of(ptr_expr: Any) -> str | None:
    """The low-limb column of a pointer expr ``lim0 + 65536*lim1``."""
    for n in sorted(names_of(ptr_expr, set())):
        if _LOW_LIMB_RE.fullmatch(n):
            return n
    return None


def base_offset_of_limb(dump: dict, low_limb: str) -> tuple[str, int] | None:
    """Recover ``(base_key, offset)`` from a low-limb decomposition constraint.

    The constraint is a product ``(Y + c)*(Y + c - 1) == 0`` with
    ``Y = SCALE*(low_limb - base0 - 256*base1)``; the offset is ``-c / SCALE``
    and ``base_key`` (e.g. ``rs1_0`` / ``read_314``) identifies the base register.
    Returns None if no such constraint is present.
    """
    for c in dump["constraints"]:
        if not (isinstance(c, list) and len(c) == 3 and c[1] == "*"):
            continue
        f = c[0]
        fn = names_of(f, set())
        if low_limb not in fn:
            continue
        if any("mem_ptr_limbs__1" in x for x in fn):     # high-limb (carry) constraint
            continue
        base0 = [x for x in fn if _BASE_RE.fullmatch(x)]
        if not base0 or any("_data__2_" in x for x in fn):
            continue
        m = _BASE_RE.fullmatch(base0[0])
        base_key = m.group(1) + "_" + m.group(2)
        k = _const_of(f)
        if k % ADDR_SCALE == 0:
            return base_key, -k // ADDR_SCALE
    return None


def recover_key(dump: dict, bi: dict) -> Key:
    """Recover the address key of a memory interaction (its ``args[1]`` pointer)."""
    ptr = bi["args"][1]
    if isinstance(ptr, int):
        return Const(to_signed(ptr))
    low = low_limb_of(ptr)
    if low is not None:
        bo = base_offset_of_limb(dump, low)
        if bo is not None:
            return BaseOffset(*bo)
    return Unresolved(Emitter().expr_str(ptr))


def address_space_of(bi: dict) -> int | None:
    """The address space (``args[0]``) if constant, else None (symbolic AS)."""
    a = bi["args"][0]
    return to_signed(a) if isinstance(a, int) else None


def classify_address_space(keys: list[Key]) -> tuple[bool, str]:
    """Can this address space be partitioned into provably-disjoint alias sets?

    Returns ``(determined, reason)``. Determined iff all keys are constant, or
    all are ``base+offset`` sharing a single base (distinct offsets ⟹ distinct).
    """
    if not keys:
        return True, "empty"
    if all(isinstance(k, Const) for k in keys):
        return True, "all-constant keys"
    if any(isinstance(k, Unresolved) for k in keys):
        return False, "unresolved symbolic keys present"
    if all(isinstance(k, BaseOffset) for k in keys):
        bases = {k.base for k in keys}  # type: ignore[attr-defined]
        if len(bases) == 1:
            return True, f"single base {next(iter(bases))} + offsets"
        return False, f"{len(bases)} distinct bases (aliasing not statically decidable)"
    return False, "mixed constant and symbolic keys"
