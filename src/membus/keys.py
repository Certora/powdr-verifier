"""Memory keys (interaction addresses) recovered from AffineDef facts.

The pointer in a memory row is an expression over address-limb columns. It is
normalized to ``base + offset`` through the **certified** affine gadget facts
(:meth:`~.rules.Analysis.affine`): a limb's defining byte-decomposition
constraint, with the root choice and no-wrap window justified per fact.

The ``BaseOffset`` label identifies the address's low-limb decomposition:
``base`` is the identity of the actual base byte columns (column identity —
two addresses computed off the same loaded register share a base), ``offset``
the recovered constant, and ``mod`` the modulus of the underlying AffineDef
fact. A finite ``mod`` (the usual case: ``2^16``, from the carry root of the
16-bit address add) means the label identifies the address **mod 2^16** —
exactly the low 16 bits, with the offset canonicalized into ``[0, mod)``.
Distinct offsets under one base are then genuinely distinct low-16 addresses.

Remaining caveats, both display/alias-level (the AS1 ``solve`` path uses only
``Const`` keys and neither applies):

- equal labels ⟹ equal addresses still relies on equal high-16 bits
  (`classify_address_space` reports a space "determined" under it);
- a pointer that does not reduce to affine-over-certified-roots is
  ``Unresolved`` and never asserted disjoint from anything.
"""
from __future__ import annotations

from dataclasses import dataclass

from . import naming
from .busmodel import MemRow
from .linform import linform
from .rules import Analysis


@dataclass(frozen=True)
class Const:
    """A constant (fixed) address."""
    value: int

    def __str__(self) -> str:
        return f"const {self.value}"


@dataclass(frozen=True)
class BaseOffset:
    """``base + offset`` — a symbolic address with a recovered constant offset.

    ``mod`` is the modulus of the identity (None = exact): the address equals
    ``base + offset`` modulo ``mod``, offset canonical in ``[0, mod)``."""
    base: str
    offset: int
    mod: int | None = None

    def __str__(self) -> str:
        return f"{self.base}+{self.offset}"


@dataclass(frozen=True)
class Unresolved:
    """A symbolic pointer that does not reduce to affine ``base+offset``."""
    expr: str

    def __str__(self) -> str:
        return f"unresolved({self.expr})"


Key = Const | BaseOffset | Unresolved


def _unresolved(ptr) -> Unresolved:
    from .busfmt import Emitter
    return Unresolved(Emitter().expr_str(ptr))


def recover_key(an: Analysis, row: MemRow) -> Key:
    """Recover the address key of a memory interaction's pointer."""
    ptr = row.ptr
    if isinstance(ptr, int):
        from src.lens.normalize import to_signed
        return Const(to_signed(ptr))
    lf = linform(ptr)
    if lf is None:                                   # nonlinear (flag-multiplexed)
        return _unresolved(ptr)
    if lf.is_const:
        return Const(lf.const)
    # limbs of the pointer that have a certified affine definition
    decs = [(col, c, an.affine(col)) for col, c in lf.items() if an.affine(col) is not None]
    if not decs:
        return _unresolved(ptr)
    # the low limb = smallest |coeff| in the pointer (the low 16 bits). The
    # modular identity only transfers to the pointer when the limb enters with
    # coefficient 1 (`ptr = limb + 2^16·high + …`); anything else is declined.
    col, c, dec = min(decs, key=lambda t: abs(t[1]))
    if c != 1:
        return _unresolved(ptr)
    weights = dict(dec.weights)
    byte0 = min((b for b, w in weights.items() if w == 1),
                default=min(weights, key=lambda b: abs(weights[b])) if weights else None)
    if byte0 is None:
        return _unresolved(ptr)
    offset = dec.offset + lf.const
    if dec.modulus is not None:
        offset %= dec.modulus
    return BaseOffset(naming.fam_access(byte0), offset, dec.modulus)


def classify_address_space(ks: list[Key]) -> tuple[bool, str]:
    """Can this address space be partitioned into provably-disjoint alias sets?

    Determined iff all keys are constant, or all are ``base+offset`` sharing a
    single base (distinct offsets ⟹ distinct, under the high-16 caveat above).
    """
    if not ks:
        return True, "empty"
    if all(isinstance(k, Const) for k in ks):
        return True, "all-constant keys"
    if any(isinstance(k, Unresolved) for k in ks):
        return False, "unresolved symbolic keys present"
    if all(isinstance(k, BaseOffset) for k in ks):
        bases = {k.base for k in ks}
        if len(bases) == 1:
            mods = {k.mod for k in ks}
            if len(mods) == 1:      # same modulus ⟹ distinct offsets ⟹ distinct
                return True, f"single base {next(iter(bases))} + offsets"
            return False, "mixed decomposition moduli (offsets not comparable)"
        return False, f"{len(bases)} distinct bases (aliasing not statically decidable)"
    return False, "mixed constant and symbolic keys"
