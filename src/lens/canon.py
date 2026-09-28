"""Factored canonical keys for dump expressions, across both representations.

powdr's two dump encodings (``machine``/``AlgebraicExpression`` and
``constraints``/``GroupedExpression``) write the same polynomial differently.
The Constraint form distributes a constant over a sum (``x - (y + 1)`` vs
``x + (p-1)*y + (p-1)``). A scalar can sit on either factor of a product
(``(f*(f-1))*c`` vs ``(c*f)*(f-1)``). And a constraint can flip sign
(``-x = 0`` vs ``x = 0``). ``canon_constraint`` in ``diff.py`` handles none of
these. The keys here handle all three without expanding products over sums.
That was checked on every guest-keccak format flip:
``powdr-research/tools/canon-diff/flip_normal_forms.py``.

A key is a *linear form*: a tuple of ``(atom, coef)`` pairs sorted by
``repr(atom)``, with every coefficient nonzero and signed (``to_signed``), and
at most one pair per atom. An atom is:

* ``ONE`` -- the constant term;
* ``("v", name)`` -- a column;
* ``("*", factors)`` -- a product of at least two *monic* linear forms (leading
  coefficient 1), sorted by ``repr``. No factor is a constant or itself a
  single product term.

``canon_value`` is the key of an expression's value (bus multiplicities and
arguments). ``canon_zero`` is the key of a constraint ``e = 0``: the value key
divided by its leading coefficient, so ``e`` and ``u*e`` get the same key for
any unit ``u``.

Soundness is machine-checked (``powdr-research/proofs/ZkvmProofs/Canon/``):
equal value keys mean equal values, and equal zero keys mean equal zero sets,
for every expression the keys accept. Anything outside the dump grammar (int,
column name, ``["-", e]``, ``[a, op, b]`` with ``op`` in ``+ - *``) raises
``CanonError`` rather than colliding.
"""
from __future__ import annotations

from typing import Any

from .metrics import FIELD_PRIME as P
from .normalize import to_signed

ONE = "1"

Lin = tuple  # tuple[(atom, int), ...]


class CanonError(ValueError):
    """The node is not a dump expression, or a coefficient has no inverse."""


def _atom_key(t: tuple) -> str:
    return repr(t[0])


def _collect(terms) -> Lin:
    """Sum coefficients of equal atoms mod p, drop zeros, sign, and sort."""
    acc: dict = {}
    for a, c in terms:
        acc[a] = (acc.get(a, 0) + c) % P
    return tuple(sorted(((a, to_signed(c)) for a, c in acc.items() if c),
                        key=_atom_key))


def _scale(lin: Lin, k: int) -> Lin:
    return _collect((a, c * k) for a, c in lin)


def _inv(c: int) -> int:
    """Inverse of ``c`` mod p. Checked, so soundness does not rest on p being prime."""
    v = pow(c % P, P - 2, P)
    if c * v % P != 1:
        raise CanonError(f"{c} has no inverse mod {P}")
    return v


def _is_prod(atom: Any) -> bool:
    return isinstance(atom, tuple) and atom[0] == "*"


def _mul(a: Lin, b: Lin) -> Lin:
    if not a or not b:
        return ()
    k = 1
    factors: list = []
    for x in (a, b):
        if len(x) == 1 and x[0][0] == ONE:          # constant
            k *= x[0][1]
        elif len(x) == 1 and _is_prod(x[0][0]):      # c * (product): flatten
            k *= x[0][1]
            factors.extend(x[0][0][1])
        else:                                        # c * (monic factor)
            c = x[0][1]
            k *= c
            factors.append(_scale(x, _inv(c)))
    if not factors:
        return _collect([(ONE, k)])
    if len(factors) == 1:
        return _scale(factors[0], k)
    return _collect([(("*", tuple(sorted(factors, key=repr))), k)])


def canon_value(node: Any) -> Lin:
    """Key of the value of a dump expression. Raises ``CanonError`` on junk."""
    if isinstance(node, bool):
        raise CanonError(f"not a dump expression: {node!r}")
    if isinstance(node, int):
        return _collect([(ONE, node)])
    if isinstance(node, str):
        return ((("v", node), 1),)
    if isinstance(node, list):
        if len(node) == 2 and node[0] == "-":
            return _scale(canon_value(node[1]), -1)
        if len(node) == 3 and node[1] in ("+", "-", "*"):
            a, b = canon_value(node[0]), canon_value(node[2])
            if node[1] == "+":
                return _collect(a + b)
            if node[1] == "-":
                return _collect(a + _scale(b, -1))
            return _mul(a, b)
    raise CanonError(f"not a dump expression: {node!r}")


def canon_zero(node: Any) -> Lin:
    """Key of the constraint ``node = 0``: the value key made monic."""
    lin = canon_value(node)
    return _scale(lin, _inv(lin[0][1])) if lin else ()


def key_cols(lin: Lin, out: set) -> None:
    """Collect the column names of a key into ``out``."""
    for atom, _ in lin:
        if isinstance(atom, tuple) and atom[0] == "v":
            out.add(atom[1])
        elif _is_prod(atom):
            for f in atom[1]:
                key_cols(f, out)
