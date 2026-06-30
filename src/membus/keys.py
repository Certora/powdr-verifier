"""Recover memory keys (the address of an interaction) and classify alias structure.

The pointer in ``args[1]`` is an expression over columns (the address limbs). We
normalize it to ``base + offset`` by **tracing the constraint that defines a limb**
— NOT by matching column names. A byte-decomposition gadget appears as a product
of two linear factors differing by a constant, ``F · (F − 1) == 0`` (so the inner
value is a bit); the in-range root ``F == 0`` gives the limb as an affine function
of the base register's bytes with integer weights and an integer offset:

    30720·lim − 30720·base0 − 7864320·base1 − 1228800 = 0
    ⟹  lim = base0 + 256·base1 + 40                       (offset 40)

The **base** is identified by the actual base columns in that gadget (their column
identity, not their family name), so two addresses computed off the same loaded
register value share a base. Only the low limb has a clean affine gadget (the high
limb is field-carry encoded), so the recovered ``base+offset`` is the low-16-bit
decomposition — exact when addresses don't differ in their high 16 bits (true for
the small heap offsets here). A pointer that doesn't reduce to affine-over-roots
(e.g. flag-multiplexed addresses) is left ``Unresolved``.

Whether an address space partitions into provably-disjoint alias sets is decidable
only when keys are pairwise distinguishable: all constant, or all ``base+offset``
sharing one base. Otherwise (multiple bases, or unresolved) aliasing is not
statically known and we flag it rather than assert disjointness.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

from src.lens.normalize import to_signed

from .order import linterms, names

# A base low-byte column is ``<family>__0_<access>@<colid>``. Used ONLY to render
# a readable label for an already-identified base column — never to *find* a base.
_FAM_RE = re.compile(r"(.+?)__0_(\d+)@\d+$")


def _product_index(dump: dict) -> dict[str, list]:
    """Column -> product constraints (``A*B``) mentioning it. Cached on the dump.

    `affine_decomp` only needs the product constraints that reference a given
    limb; this index makes that O(few) instead of scanning all constraints.
    """
    idx = dump.get("_membus_prod_index")
    if idx is None:
        idx = {}
        for c in dump.get("constraints", []):
            if isinstance(c, list) and len(c) == 3 and c[1] == "*":
                for col in names(c):
                    idx.setdefault(col, []).append(c)
        dump["_membus_prod_index"] = idx
    return idx


def _range_checked(dump: dict) -> set[str]:
    """Columns proven bounded by a range-check bus (VariableRangeChecker id 3 /
    BitwiseLookup 6 / TupleRangeChecker 7). Cached on the dump.

    Selecting the integer root of the ``F·(F−1)`` gadget is sound only if the
    decomposed limb is a bounded integer — i.e. range-checked. We verify it.
    """
    rc = dump.get("_membus_range_checked")
    if rc is None:
        rc = set()
        for b in dump.get("bus_interactions", []):
            if b.get("id") in (3, 6, 7):
                for a in b["args"]:
                    names(a, rc)
        dump["_membus_range_checked"] = rc
    return rc


def _bounded(dump: dict) -> set[str]:
    """Columns proven to hold bounded integers (bytes): range-checked columns,
    plus the data bytes (args[2:6]) of memory-bus interactions.

    The latter relies on the invariant that **everything on the memory bus is a
    byte** — reads are assumed byte-valued, writes are checked separately, and
    prior basic blocks uphold the same. This is what bounds the base register
    bytes (e.g. ``rs1_data``) that the address decomposition is computed from.
    """
    b = dump.get("_membus_bounded")
    if b is None:
        b = set(_range_checked(dump))
        for bi in dump.get("bus_interactions", []):
            if bi.get("id") == 1:
                for a in bi["args"][2:6]:        # b0..b3 data bytes
                    names(a, b)
        dump["_membus_bounded"] = b
    return b


@dataclass(frozen=True)
class Const:
    """A constant (fixed) address."""
    value: int

    def __str__(self) -> str:
        return f"const {self.value}"


@dataclass(frozen=True)
class BaseOffset:
    """``base + offset`` — a symbolic address with a recovered constant offset.

    ``base`` is a readable, 1:1 label of the recovered base register value
    (``rs1_0`` = the rs1 value loaded at access 0, ``read_314``, ``a_0``, …);
    distinct loaded values get distinct labels, so it doubles as the alias key.
    """
    base: str
    offset: int

    def __str__(self) -> str:
        return f"{self.base}+{self.offset}"


@dataclass(frozen=True)
class Unresolved:
    """A symbolic pointer that does not reduce to affine ``base+offset``."""
    expr: str

    def __str__(self) -> str:
        return f"unresolved({self.expr})"


Key = Const | BaseOffset | Unresolved


def _fam_access(col: str) -> str:
    """Readable label for a base low-byte column (``rs1_data__0_0@3`` -> ``rs1_0``)."""
    m = _FAM_RE.fullmatch(col)
    if not m:
        return col
    fam = m.group(1)
    fam = fam[:-5] if fam.endswith("_data") else fam   # rs1_data -> rs1, read_data -> read
    return f"{fam}_{m.group(2)}"


def affine_decomp(dump: dict, col: str) -> tuple[dict[str, int], int] | None:
    """If ``col`` is defined by a byte-decomposition gadget, return its affine form.

    Looks for a constraint ``F · (F ± 1) == 0`` (a product of two linear factors
    differing by a constant) with ``col`` in a factor ``F``. Solving ``F == 0`` for
    ``col`` must give **integer** weights on the other columns and an **integer**
    offset (this selects the in-range root and confirms a clean affine relation).
    Returns ``(weights, offset)`` so that ``col == Σ weights·other + offset``, or
    None. No column-name matching — the gadget is recognized structurally.

    Integer-root selection is sound only if every column in the factor is a
    bounded integer: the limb ``col`` must be range-checked, and the base columns
    must be bounded (range-checked or memory-bus data bytes). Otherwise we decline.
    """
    if col not in _range_checked(dump):
        return None
    bounded = _bounded(dump)
    for c in _product_index(dump).get(col, []):
        fa, fb = linterms(c[0]), linterms(c[2])
        if fa is None or fb is None:
            continue
        # the two factors must differ only by a constant (the `F·(F−1)` bit gadget)
        if fa[0] != fb[0]:
            continue
        for coeffs, const in (fa, fb):
            a = coeffs.get(col)
            if not a:
                continue
            others = {k: v for k, v in coeffs.items() if k != col and v != 0}
            if any(o not in bounded for o in others):     # base must be bounded bytes
                continue
            if any(v % a != 0 for v in others.values()) or const % a != 0:
                continue
            weights = {k: -(v // a) for k, v in others.items()}
            return weights, -(const // a)
    return None


def recover_key(dump: dict, bi: dict) -> Key:
    """Recover the address key of a memory interaction (its ``args[1]`` pointer)."""
    ptr = bi["args"][1]
    if isinstance(ptr, int):
        return Const(to_signed(ptr))
    lt = linterms(ptr)
    if lt is None:                                   # nonlinear (e.g. flag-multiplexed)
        from .busfmt import Emitter
        return Unresolved(Emitter().expr_str(ptr))
    coeffs, const = {k: v for k, v in lt[0].items() if v != 0}, lt[1]
    if not coeffs:
        return Const(const)
    # decomposable columns of the pointer (the limbs that have an affine gadget)
    decs = [(k, d) for k in coeffs if (d := affine_decomp(dump, k)) is not None]
    if not decs:
        from .busfmt import Emitter
        return Unresolved(Emitter().expr_str(ptr))
    # use the low limb (smallest |coeff| in the pointer = the low 16 bits)
    col, (weights, off) = min(decs, key=lambda kd: abs(coeffs[kd[0]]))
    # base = the byte-0 base column (weight 1); offset = pointer's affine offset
    byte0 = min((b for b, w in weights.items() if w == 1),
                default=min(weights, key=lambda b: abs(weights[b])) if weights else None)
    if byte0 is None:
        from .busfmt import Emitter
        return Unresolved(Emitter().expr_str(ptr))
    return BaseOffset(_fam_access(byte0), coeffs[col] * off + const)


def address_space_of(bi: dict) -> int | None:
    """The address space (``args[0]``) if constant, else None (symbolic AS)."""
    a = bi["args"][0]
    return to_signed(a) if isinstance(a, int) else None


def classify_address_space(keys: list[Key]) -> tuple[bool, str]:
    """Can this address space be partitioned into provably-disjoint alias sets?

    Determined iff all keys are constant, or all are ``base+offset`` sharing a
    single base (distinct offsets ⟹ distinct). Returns ``(determined, reason)``.
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
