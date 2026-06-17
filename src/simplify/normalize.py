"""Canonicalize polynomial ``Int`` relations.

Each monomial is an exponent tuple ``(e_0, …, e_{n-1})`` aligned with a fixed variable order
(see ``collect_variables``). Monomials are compared by **graded lex** (total degree, then
lexicographic on exponents).

**Field mod equalities**: monic normalization via ``field_eq`` when ``relation_poly_diff`` reports
modular. **Other equalities and inequalities**: gcd-normalized diff, with ``wrap_mod`` on
inequalities when modular.
"""

from __future__ import annotations

from functools import cmp_to_key, reduce
from math import gcd

from pysmt.walkers import IdentityDagWalker

from ..smt.utils import *
from ..utils.args import ARGS

Monomial = tuple[int, ...]
Poly = dict[Monomial, int]


def _field_modulus() -> int:
    """Field prime ``p`` for modular coefficient arithmetic."""
    return int(ARGS().field_type.value)


def _is_combinator(n: FNode) -> bool:
    """Arithmetic nodes that ``_expr_to_poly`` decomposes rather than treats as a ring atom."""
    return n.is_plus() or n.is_minus() or n.is_times()


def collect_variables(smt_script: script.SmtLibScript) -> tuple[FNode, ...]:
    """Atomic ring generators across all ``assert`` bodies, in a deterministic order.

    A generator is any ``Int`` subterm that ``_expr_to_poly`` treats atomically: an ``Int``
    symbol, **or** a maximal **opaque** ``Int`` node — e.g. an uninterpreted ``uf_and(…)``
    bitwise application — that is neither an integer constant nor an ``+``/``-``/``*``
    combinator. Opaque nodes are *not* descended into: the whole node is one generator (so
    its internal structure never leaks extra generators). Field ``(mod body p)`` wrappers are
    transparent here because relation walkers unwrap them before parsing ``body``.

    Treating bitwise/uninterpreted terms as generators (rather than bailing) is what lets the
    monic rewrite reach booleanity atoms like ``(= (mod (… + c·uf_and(a,3)) p) 0)``.
    """
    gens: set[FNode] = set()
    seen: set[FNode] = set()  # assert bodies are shared DAGs — visit each node once

    def visit(n: FNode) -> None:
        if n in seen:
            return
        seen.add(n)
        if n.get_type().is_int_type():
            if _as_int_const(n) is not None:
                return
            if _field_mod_wrap(n):
                visit(n.arg(0))
                return
            if _is_combinator(n):
                for a in n.args():
                    visit(a)
                return
            gens.add(n)
            return
        for a in n.args():
            visit(a)

    for cmd in smt_script.commands:
        if cmd.name == "assert":
            visit(cmd.args[0])
    return tuple(sorted(gens, key=lambda s: s.serialize()))


def _compare_monomials(e1: Monomial, e2: Monomial) -> int:
    """Comparator for graded lex; return value suitable for ``cmp_to_key`` (``>`` means ``e1`` larger)."""
    s1, s2 = sum(e1), sum(e2)
    if s1 != s2:
        return 1 if s1 > s2 else -1
    for a, b in zip(e1, e2, strict=True):
        if a != b:
            return 1 if a > b else -1
    return 0


def _lead_exp(poly: Poly) -> Monomial:
    """Leading monomial under graded lex (``_compare_monomials``)."""
    return max(poly, key=cmp_to_key(_compare_monomials))


def _poly_add(a: Poly, b: Poly, scale_b: int, *, mod: int | None) -> Poly:
    """Coefficient-wise ``a + scale_b * b``; drops zero coefficients."""
    out: Poly = {}
    for e in a.keys() | b.keys():
        v = a.get(e, 0) + scale_b * b.get(e, 0)
        if mod is not None:
            v %= mod
        if v:
            out[e] = v
    return out


def _poly_mul(a: Poly, b: Poly, n: int, *, mod: int | None) -> Poly:
    """Polynomial product: exponents add componentwise; coefficients multiply (mod ``mod`` if set)."""
    out: Poly = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = tuple(e1[i] + e2[i] for i in range(n))
            v = out.get(e, 0) + c1 * c2
            if mod is not None:
                v %= mod
            out[e] = v
    return {e: c for e, c in out.items() if c}


def _as_int_const(n: FNode) -> int | None:
    """Literal integer value, or ``None`` if ``n`` is not an ``Int`` constant."""
    if n.node_type() == operators.INT_CONSTANT:
        return int(n.constant_value())
    return None


def _field_mod_wrap(e: FNode) -> bool:
    """True if ``e`` is ``(mod _ p)`` with literal ``p`` equal to the configured field modulus."""
    return e.is_mod() and _as_int_const(e.arg(1)) == _field_modulus()


def _relation_modular(lhs: FNode, rhs: FNode) -> bool | None:
    """``True``/``False`` when sides agree on field mod; constants are neutral; else ``None``."""
    lhs_m = _field_mod_wrap(lhs)
    rhs_m = _field_mod_wrap(rhs)
    if lhs_m == rhs_m:
        return lhs_m
    if lhs_m and _as_int_const(rhs) is not None:
        return True
    if rhs_m and _as_int_const(lhs) is not None:
        return True
    return None


def _unwrap_field_mod_body(e: FNode) -> FNode:
    if _field_mod_wrap(e):
        return e.arg(0)
    return e


def relation_poly_diff(
    lhs: FNode,
    rhs: FNode,
    var_index: dict[FNode, int],
    vars_: tuple[FNode, ...],
) -> tuple[Poly, bool] | None:
    """Parse ``Int`` sides into ``(lhs - rhs, modular)``.

    ``modular`` is ``True`` when field ``(mod … p)`` appears on either side (integer constants
    count as neutral). Returns ``None`` on non-``Int`` sides, mod/plain mismatch, or parse failure.
    """
    if not (lhs.get_type().is_int_type() and rhs.get_type().is_int_type()):
        return None
    if (modular := _relation_modular(lhs, rhs)) is None:
        return None
    mod = _field_modulus() if modular else None
    diff = _poly_diff_poly(
        _unwrap_field_mod_body(lhs),
        _unwrap_field_mod_body(rhs),
        var_index,
        len(vars_),
        mod=mod,
    )
    if diff is None:
        return None
    return diff, modular


def _expr_to_poly(
    n: FNode,
    var_index: dict[FNode, int],
    nvars: int,
    *,
    mod: int | None,
) -> Poly | None:
    """Parse an ``Int`` polynomial built from ``+``, unary ``-``, ``*``, constants, symbols."""
    if (ic := _as_int_const(n)) is not None:
        m = ic % mod if mod is not None else ic
        return {(0,) * nvars: m} if m else {}
    if n.is_plus():
        acc: Poly | None = {}
        for a in n.args():
            q = _expr_to_poly(a, var_index, nvars, mod=mod)
            if q is None:
                return None
            acc = _poly_add(acc, q, 1, mod=mod)
        return acc
    if n.is_minus():
        if len(n.args()) != 2:
            return None
        a, b = n.args()
        pa = _expr_to_poly(a, var_index, nvars, mod=mod)
        pb = _expr_to_poly(b, var_index, nvars, mod=mod)
        if pa is None or pb is None:
            return None
        return _poly_add(pa, pb, -1, mod=mod)
    if n.is_times():
        acc = {(0,) * nvars: 1}
        for a in n.args():
            q = _expr_to_poly(a, var_index, nvars, mod=mod)
            if q is None:
                return None
            acc = _poly_mul(acc, q, nvars, mod=mod)
            assert acc is not None
        return acc
    if n in var_index:
        e = [0] * nvars
        e[var_index[n]] = 1
        return {tuple(e): 1}
    return None


def _poly_to_expr(poly: Poly, vars_: tuple[FNode, ...]) -> FNode:
    """``Poly`` → PySMT sum; monomials emitted in descending graded lex (stable printer order)."""
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


def _poly_diff_poly(
    la: FNode,
    lb: FNode,
    var_index: dict[FNode, int],
    nvars: int,
    *,
    mod: int | None,
) -> Poly | None:
    pla = _expr_to_poly(la, var_index, nvars, mod=mod)
    plb = _expr_to_poly(lb, var_index, nvars, mod=mod)
    if pla is None or plb is None:
        return None
    return _poly_add(pla, plb, -1, mod=mod)


def _rescale_monic(poly: Poly, mod: int) -> Poly:
    """Multiply by ``lc^{-1}`` in ``F_mod`` so the leading coefficient is ``1``."""
    out = {e: c for e, c in poly.items() if c}
    lc = out[_lead_exp(out)]
    assert lc != 0
    inv = pow(lc, -1, mod)
    return {e: v for e, c in out.items() if (v := (c * inv) % mod)}


def _rescale_gcd(poly: Poly) -> Poly:
    """Divide all coefficients by their gcd; leading coefficient positive."""
    if not poly:
        return poly
    g = reduce(gcd, (abs(c) for c in poly.values()))
    if g == 0:
        return {}
    lc = poly[_lead_exp(poly)]
    if lc < 0:
        g = -g
    return {e: c // g for e, c in poly.items() if c // g}


def normalize_int_rel_gcd(
    lhs: FNode,
    rhs: FNode,
    var_index: dict[FNode, int],
    vars_: tuple[FNode, ...],
) -> FNode | None:
    """Gcd-normalized ``lhs - rhs`` for inequalities (``wrap_mod`` when modular)."""
    parsed = relation_poly_diff(lhs, rhs, var_index, vars_)
    if parsed is None:
        return None
    diff, modular = parsed
    if not diff:
        rep = Int(0)
    else:
        rep = _poly_to_expr(_rescale_gcd(diff), vars_)
    if modular:
        return wrap_mod(rep)
    return rep


class _NormalizeWalker(IdentityDagWalker):
    """DAG rewrite: field-mod equalities (monic) and other ``Int`` relations (gcd / mod)."""

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
        parsed = relation_poly_diff(lhs, rhs, self._vi, self._vt)
        if parsed is None:
            return keep_comment(self.mgr.Equals(lhs, rhs), formula)
        diff, modular = parsed
        if not diff:
            rep = Int(0)
        elif modular:
            rep = _poly_to_expr(_rescale_monic(diff, _field_modulus()), self._vt)
        else:
            rep = _poly_to_expr(_rescale_gcd(diff), self._vt)
        if modular:
            return keep_comment(field_eq(rep), formula)
        return keep_comment(Equals(rep, Int(0)), formula)

    def walk_lt(self, formula, args, **kwargs):
        lhs, rhs = args
        rep = normalize_int_rel_gcd(lhs, rhs, self._vi, self._vt)
        if rep is None:
            return keep_comment(self.mgr.LT(lhs, rhs), formula)
        return keep_comment(LT(rep, Int(0)), formula)

    def walk_le(self, formula, args, **kwargs):
        lhs, rhs = args
        rep = normalize_int_rel_gcd(lhs, rhs, self._vi, self._vt)
        if rep is None:
            return keep_comment(self.mgr.LE(lhs, rhs), formula)
        return keep_comment(LE(rep, Int(0)), formula)


def simplify_normalize(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Walk every ``assert`` and normalize matching polynomial equalities in place."""
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
