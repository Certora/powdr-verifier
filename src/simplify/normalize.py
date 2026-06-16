"""Canonicalize polynomial equalities over ``F_p`` (``ARGS().field_type``), graded lex on exponent tuples.

``Poly`` maps monomials to coefficients already reduced mod ``p`` (``_coeff_mod``).
Only ``(= (mod … p) 0)`` with ``p`` the field modulus is rewritten; other ``Int`` equalities are left unchanged.
"""

from __future__ import annotations

from functools import cmp_to_key

from pysmt.walkers import IdentityDagWalker

from ..smt.utils import *
from ..utils.args import ARGS

Monomial = tuple[int, ...]
Poly = dict[Monomial, int]


def _field_modulus() -> int:
    return int(ARGS().field_type.value)


def collect_variables(smt_script: script.SmtLibScript) -> tuple[FNode, ...]:
    syms: set[FNode] = set()
    for cmd in smt_script.commands:
        if cmd.name == "assert":
            syms |= {
                v
                for v in cmd.args[0].get_free_variables()
                if v.get_type().is_int_type()
            }
    return tuple(sorted(syms, key=lambda s: s.symbol_name()))


def _compare_monomials(e1: Monomial, e2: Monomial) -> int:
    s1, s2 = sum(e1), sum(e2)
    if s1 != s2:
        return 1 if s1 > s2 else -1
    for a, b in zip(e1, e2, strict=True):
        if a != b:
            return 1 if a > b else -1
    return 0


def _lead_exp(poly: Poly) -> Monomial:
    return max(poly, key=cmp_to_key(_compare_monomials))


def _poly_add(a: Poly, b: Poly, scale_b: int) -> Poly:
    p = _field_modulus()
    return {
        e: v
        for e in a.keys() | b.keys()
        if (v := (a.get(e, 0) + scale_b * b.get(e, 0)) % p)
    }


def _poly_mul(a: Poly, b: Poly, n: int) -> Poly:
    p = _field_modulus()
    out: Poly = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = tuple(e1[i] + e2[i] for i in range(n))
            out[e] = (out.get(e, 0) + c1 * c2) % p
    return {e: c for e, c in out.items() if c}


def _as_int_const(n: FNode) -> int | None:
    if n.node_type() == operators.INT_CONSTANT:
        return int(n.constant_value())
    return None


def _field_mod_wrap(e: FNode) -> bool:
    return e.is_mod() and _as_int_const(e.arg(1)) == _field_modulus()


def _expr_to_poly(
    n: FNode,
    var_index: dict[FNode, int],
    nvars: int,
) -> Poly | None:
    p = _field_modulus()
    if (ic := _as_int_const(n)) is not None:
        m = ic % p
        return {(0,) * nvars: m} if m else {}
    if n.is_symbol() and n.symbol_type().is_int_type():
        assert n in var_index
        e = [0] * nvars
        e[var_index[n]] = 1
        return {tuple(e): 1}
    if n.is_plus():
        acc: Poly | None = {}
        for a in n.args():
            q = _expr_to_poly(a, var_index, nvars)
            if q is None:
                return None
            acc = _poly_add(acc, q, 1)
        return acc
    if n.is_minus():
        if len(n.args()) != 2:
            return None
        a, b = n.args()
        pa = _expr_to_poly(a, var_index, nvars)
        pb = _expr_to_poly(b, var_index, nvars)
        if pa is None or pb is None:
            return None
        return _poly_add(pa, pb, -1)
    if n.is_times():
        acc = {(0,) * nvars: 1}
        for a in n.args():
            q = _expr_to_poly(a, var_index, nvars)
            if q is None:
                return None
            acc = _poly_mul(acc, q, nvars)
            assert acc is not None
        return acc
    return None


def _poly_to_expr(poly: Poly, vars_: tuple[FNode, ...]) -> FNode:
    if not poly:
        return Int(0)
    items = sorted(poly.items(), key=cmp_to_key(lambda x, y: -_compare_monomials(x[0], y[0])))
    terms: list[FNode] = []
    for e, c in items:
        if c == 0:
            continue
        mono_factors: list[FNode] = []
        for i, ei in enumerate(e):
            mono_factors.extend([vars_[i]] * ei)
        if not mono_factors:
            terms.append(Int(c))
        elif c == 1:
            terms.append(Times(*mono_factors) if len(mono_factors) > 1 else mono_factors[0])
        else:
            terms.append(Times(Int(c), *mono_factors))
    if not terms:
        return Int(0)
    if len(terms) == 1:
        return terms[0]
    return Plus(*terms)


def _rescale_monic_field(poly: Poly) -> Poly:
    p = _field_modulus()
    out = {e: c for e, c in poly.items() if c}
    lc = out[_lead_exp(out)]
    assert lc != 0
    inv = pow(lc, -1, p)
    return {
        e: v
        for e, c in out.items()
        if (v := (c * inv) % p)
    }


def _normalize_int_poly_eq(
    a: FNode,
    var_index: dict[FNode, int],
    vars_: tuple[FNode, ...],
) -> FNode | None:
    pa = _expr_to_poly(a, var_index, len(vars_))
    if pa is None:
        return None
    return _poly_to_expr(_rescale_monic_field(pa), vars_)


class _NormalizeWalker(IdentityDagWalker):
    def __init__(
        self,
        var_index: dict[FNode, int],
        vars_: tuple[FNode, ...],
        *,
        env=None,
    ):
        super().__init__(env=env)
        self._vi = var_index
        self._vt = vars_

    def walk_equals(self, formula, args, **kwargs):
        lhs, rhs = args
        if not (lhs.get_type().is_int_type() and rhs.get_type().is_int_type()):
            return self.mgr.Equals(lhs, rhs)
        if not (_field_mod_wrap(lhs) and _as_int_const(rhs) == 0):
            return self.mgr.Equals(lhs, rhs)
        rep = _normalize_int_poly_eq(lhs.arg(0), self._vi, self._vt)
        if rep is None:
            return self.mgr.Equals(lhs, rhs)
        return keep_comment(field_eq(rep), formula)


def simplify_normalize(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    vars_sorted = collect_variables(smt_script)
    var_index = {s: i for i, s in enumerate(vars_sorted)}
    walker = _NormalizeWalker(var_index, vars_sorted, env=get_env())
    changed = total = 0
    for cmd in smt_script.commands:
        if cmd.name != "assert":
            continue
        total += 1
        old = cmd.args[0]
        new = walker.walk(old)
        cmd.args[0] = new
        if new != old:
            changed += 1
    if subaction is not None:
        subaction += {"asserts": total, "asserts_changed": changed, "int_vars": len(vars_sorted)}
    return smt_script
