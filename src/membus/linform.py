"""Canonical linear forms over BabyBear — the single normalization layer.

Every extraction rule consumes dump expressions through this module, never raw
JSON. A dump expression parses to exactly one of:

- :class:`LinForm` — a linear polynomial ``Σ coeff·col + const`` with every
  coefficient and the constant in **canonical signed residue form**
  (``to_signed`` of the value mod p). Zero coefficients are dropped.
- :class:`Product` — a product of two linear factors (the shape of the
  ``F·(F−δ)`` selector/decomposition gadgets).
- ``None`` — anything else (higher degree, unsupported ops). Rules must
  decline on None; there is no partial parse.

Canonical signing matters for correctness, not just neatness: rules compare
coefficients against ±1, test divisibility, and read constants as integer
gaps. Those tests are only meaningful on the canonical representative — the
same field element must never appear as two different integers (e.g. an
accumulated constant of exactly ``p`` must be ``0``, not ``p``).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterator

from src.lens.normalize import BABYBEAR_PRIME, to_signed


def _canon(v: int) -> int:
    """Canonical signed representative of ``v`` mod p, in (−p/2, p/2]."""
    return to_signed(v % BABYBEAR_PRIME)


@dataclass(frozen=True)
class LinForm:
    """``Σ coeffs[col]·col + const`` with canonical signed integer entries."""

    coeffs: tuple[tuple[str, int], ...]   # sorted by column name, no zeros
    const: int

    @staticmethod
    def make(coeffs: dict[str, int], const: int) -> "LinForm":
        cc = {k: _canon(v) for k, v in coeffs.items()}
        return LinForm(tuple(sorted((k, v) for k, v in cc.items() if v != 0)),
                       _canon(const))

    def coeff(self, col: str) -> int:
        for k, v in self.coeffs:
            if k == col:
                return v
        return 0

    @property
    def columns(self) -> tuple[str, ...]:
        return tuple(k for k, _ in self.coeffs)

    def items(self) -> Iterator[tuple[str, int]]:
        return iter(self.coeffs)

    @property
    def is_const(self) -> bool:
        return not self.coeffs

    def __str__(self) -> str:
        parts = [f"{v}*{k}" for k, v in self.coeffs]
        if self.const or not parts:
            parts.append(str(self.const))
        return " + ".join(parts)


@dataclass(frozen=True)
class Product:
    """A constraint of shape ``left · right`` (each factor linear)."""

    left: LinForm
    right: LinForm


def _linterms(e: Any) -> tuple[dict[str, int], int] | None:
    """Raw linear parse (unnormalized accumulation); None if nonlinear."""
    if isinstance(e, bool):
        return None
    if isinstance(e, int):
        return {}, e
    if isinstance(e, str):
        return {e: 1}, 0
    if isinstance(e, list) and len(e) == 2 and e[0] == "-":      # unary minus
        inner = _linterms(e[1])
        if inner is None:
            return None
        return {k: -v for k, v in inner[0].items()}, -inner[1]
    if isinstance(e, list) and len(e) == 3:
        a, op, b = e
        la, lb = _linterms(a), _linterms(b)
        if la is None or lb is None:
            return None
        if op in ("+", "-"):
            s = 1 if op == "+" else -1
            d = dict(la[0])
            for k, v in lb[0].items():
                d[k] = d.get(k, 0) + s * v
            return d, la[1] + s * lb[1]
        if op == "*":
            if not la[0]:
                s = la[1]
                return {k: s * v for k, v in lb[0].items()}, s * lb[1]
            if not lb[0]:
                s = lb[1]
                return {k: s * v for k, v in la[0].items()}, s * la[1]
            return None
        return None
    return None


def linform(e: Any) -> LinForm | None:
    """Parse a dump expression into a canonical :class:`LinForm`, or None."""
    lt = _linterms(e)
    if lt is None:
        return None
    return LinForm.make(lt[0], lt[1])


def product(e: Any) -> Product | None:
    """Parse a top-level binary product of two linear factors, or None."""
    if isinstance(e, list) and len(e) == 3 and e[1] == "*":
        left, right = linform(e[0]), linform(e[2])
        if left is not None and right is not None:
            return Product(left, right)
    return None


_OPS = ("+", "-", "*")


def names(e: Any, acc: set[str] | None = None) -> set[str]:
    """All column names referenced anywhere in a dump expression.

    Operator tokens (the middle string of ``[a, op, b]`` / the head of
    ``["-", e]``) are not columns and are skipped.
    """
    if acc is None:
        acc = set()
    if isinstance(e, str):
        if e not in _OPS:
            acc.add(e)
    elif isinstance(e, list):
        for x in e:
            names(x, acc)
    return acc
