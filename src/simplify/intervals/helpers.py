"""Low-level shape predicates on PySMT nodes for interval extraction (affine, mod, etc.)."""
from __future__ import annotations

from typing import Dict, Optional

from pysmt import operators

from ...smt.utils import FNode
from .domain import IntDomain, IntInterval


def _is_int_const(n: FNode) -> Optional[int]:
    """Safe int constant extraction (avoids ``is_int_constant()`` on arbitrary nodes)."""
    # Do not call is_int_constant() on arbitrary nodes: pySMT can raise on array values.
    if n.node_type() == operators.INT_CONSTANT:
        return int(n.constant_value())
    return None


def _is_bool_const(n: FNode) -> Optional[bool]:
    """Return bool constant value or ``None``."""
    if n.node_type() == operators.BOOL_CONSTANT:
        return bool(n.constant_value())
    return None


def _is_mod_p(n: FNode, p: int) -> Optional[FNode]:
    """If ``n`` is ``(mod e p)`` with constant modulus ``p``, return ``e``."""
    if not n.is_mod():
        return None
    a, m = n.args()
    if _is_int_const(m) == p:
        return a
    return None


def _affine(e: FNode) -> Optional[tuple[int, Dict[FNode, int]]]:
    """Parse e as const + sum(coeff_i * sym_i), else return None."""

    def add_maps(a: Dict[FNode, int], b: Dict[FNode, int], k: int = 1) -> Dict[FNode, int]:
        """Pointwise ``a + k*b`` on coefficient maps, dropping zero coefficients."""
        out = dict(a)
        for s, c in b.items():
            out[s] = out.get(s, 0) + k * c
            if out[s] == 0:
                del out[s]
        return out

    if (c := _is_int_const(e)) is not None:
        return c, {}
    if e.is_symbol():
        return 0, {e: 1}
    if e.is_plus():
        c0 = 0
        m: Dict[FNode, int] = {}
        for a in e.args():
            sub = _affine(a)
            if sub is None:
                return None
            c, mm = sub
            c0 += c
            m = add_maps(m, mm)
        return c0, m
    if e.is_minus():
        a, b = e.args()
        aa, bb = _affine(a), _affine(b)
        if aa is None or bb is None:
            return None
        ca, ma = aa
        cb, mb = bb
        return ca - cb, add_maps(ma, mb, -1)
    if e.is_times():
        const_prod = 1
        nonconst = []
        for a in e.args():
            if (c := _is_int_const(a)) is not None:
                const_prod *= c
            else:
                nonconst.append(a)
        if len(nonconst) == 0:
            return const_prod, {}
        if len(nonconst) != 1:
            return None
        sub = _affine(nonconst[0])
        if sub is None:
            return None
        c, m = sub
        return c * const_prod, {s: coeff * const_prod for s, coeff in m.items()}
    return None


def _ceil_div(a: int, b: int) -> int:
    """Ceiling of ``a/b`` for ``b > 0``."""
    assert b > 0
    return -((-a) // b)


def _unique_multiple_in_interval(iv: IntInterval, p: int) -> Optional[int]:
    """Return the unique multiple of p in iv, or None if not unique/unknown."""
    if iv.lo is None or iv.hi is None:
        return None
    k_lo = _ceil_div(iv.lo, p)
    k_hi = iv.hi // p
    if k_lo != k_hi:
        return None
    return k_lo * p


def _unique_multiple_in_domain(dom: IntDomain, p: int) -> Optional[int]:
    """Unique multiple of ``p`` in abstract domain ``dom``, if any and unique on the hull."""
    hull = dom.hull()
    uniq = _unique_multiple_in_interval(hull, p)
    if uniq is None:
        return None
    return uniq if dom.contains(uniq) else None
