from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Optional

from pysmt import operators

from ..smt.utils import *


INF = None


@dataclass(frozen=True)
class Interval:
    lo: Optional[int]
    hi: Optional[int]

    @staticmethod
    def top() -> "Interval":
        return Interval(INF, INF)

    @staticmethod
    def const(v: int) -> "Interval":
        return Interval(v, v)

    def is_bottom(self) -> bool:
        return self.lo is not None and self.hi is not None and self.lo > self.hi

    def intersect(self, other: "Interval") -> "Interval":
        lo = other.lo if self.lo is None else (self.lo if other.lo is None else max(self.lo, other.lo))
        hi = other.hi if self.hi is None else (self.hi if other.hi is None else min(self.hi, other.hi))
        return Interval(lo, hi)

    def add(self, other: "Interval") -> "Interval":
        lo = None if self.lo is None or other.lo is None else self.lo + other.lo
        hi = None if self.hi is None or other.hi is None else self.hi + other.hi
        return Interval(lo, hi)

    def neg(self) -> "Interval":
        lo = None if self.hi is None else -self.hi
        hi = None if self.lo is None else -self.lo
        return Interval(lo, hi)

    def sub(self, other: "Interval") -> "Interval":
        return self.add(other.neg())

    def mul(self, other: "Interval") -> "Interval":
        if self.lo is None or self.hi is None or other.lo is None or other.hi is None:
            return Interval.top()
        vals = [
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        ]
        return Interval(min(vals), max(vals))

    def scale(self, k: int) -> "Interval":
        if k == 0:
            return Interval.const(0)
        if self.lo is None or self.hi is None:
            return Interval.top()
        a, b = self.lo * k, self.hi * k
        return Interval(min(a, b), max(a, b))

    def within_0_p(self, p: int) -> bool:
        return self.lo is not None and self.hi is not None and 0 <= self.lo and self.hi < p


def _is_int_const(n: FNode) -> Optional[int]:
    if n.node_type() == operators.INT_CONSTANT:
        return int(n.constant_value())
    return None


def _is_bool_const(n: FNode) -> Optional[bool]:
    if n.node_type() == operators.BOOL_CONSTANT:
        return bool(n.constant_value())
    return None


def _flatten_and(f: FNode) -> Iterable[FNode]:
    if f.is_and():
        for a in f.args():
            yield from _flatten_and(a)
    else:
        yield f


def _ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


def _floor_div(a: int, b: int) -> int:
    assert b > 0
    return a // b


def _unique_multiple_in_interval(iv: Interval, p: int) -> Optional[int]:
    """Return the unique multiple of p in iv, or None if not unique/unknown."""
    if iv.lo is None or iv.hi is None:
        return None
    k_lo = _ceil_div(iv.lo, p)
    k_hi = iv.hi // p
    if k_lo != k_hi:
        return None
    return k_lo * p


def _affine(e: FNode) -> Optional[tuple[int, Dict[FNode, int]]]:
    """Parse e as const + sum(coeff_i * sym_i), else return None."""

    def add_maps(a: Dict[FNode, int], b: Dict[FNode, int], k: int = 1) -> Dict[FNode, int]:
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


class IntervalICPEngine:
    """Fixed-point interval propagation over integers with modular-aware refinements."""

    def __init__(self, p: Optional[int] = None):
        self.p = int(ARGS().field_type.value if p is None else p)
        self.env: Dict[FNode, Interval] = {}
        self._cache: Dict[FNode, Interval] = {}
        self.inconsistent = False
        self.tightened_symbols: set[FNode] = set()
        self.strengthening_formulas: set[FNode] = set()

    def _default_interval(self, sym: FNode) -> Interval:
        # Start in the full integer domain. Field bounds are learned from
        # constraints (e.g. 0 <= x, x < p), not assumed a priori.
        return Interval.top()

    def get_interval(self, sym: FNode) -> Interval:
        if sym in self.env:
            return self.env[sym]
        if sym.is_symbol() and sym.get_type().is_int_type():
            self.env[sym] = self._default_interval(sym)
            return self.env[sym]
        return Interval.top()

    def _set_interval(self, sym: FNode, iv: Interval) -> bool:
        old = self.get_interval(sym)
        new = old.intersect(iv)
        if new.is_bottom():
            self.inconsistent = True
        if new == old:
            return False
        self.env[sym] = new
        self.tightened_symbols.add(sym)
        self._cache.clear()
        return True

    def _eval_int(self, e: FNode) -> Interval:
        if e in self._cache:
            return self._cache[e]

        if (c := _is_int_const(e)) is not None:
            out = Interval.const(c)
        elif e.is_symbol():
            out = self.get_interval(e)
        elif e.is_plus():
            acc = Interval.const(0)
            for a in e.args():
                acc = acc.add(self._eval_int(a))
            out = acc
        elif e.is_minus():
            a, b = e.args()
            out = self._eval_int(a).sub(self._eval_int(b))
        elif e.is_times():
            acc = Interval.const(1)
            for a in e.args():
                acc = acc.mul(self._eval_int(a))
            out = acc
        elif e.is_mod():
            a, m = e.args()
            mv = _is_int_const(m)
            if mv is not None and mv > 0:
                ai = self._eval_int(a)
                if ai.within_0_p(mv):
                    out = ai
                else:
                    out = Interval(0, mv - 1)
            else:
                out = Interval.top()
        else:
            out = Interval.top()

        self._cache[e] = out
        return out

    def eval_bool(self, f: FNode) -> Optional[bool]:
        if (bc := _is_bool_const(f)) is not None:
            return bc
        if f.is_not():
            v = self.eval_bool(f.arg(0))
            return None if v is None else (not v)
        if f.is_and():
            vals = [self.eval_bool(a) for a in f.args()]
            if False in vals:
                return False
            if None in vals:
                return None
            return True
        if f.is_or():
            vals = [self.eval_bool(a) for a in f.args()]
            if True in vals:
                return True
            if None in vals:
                return None
            return False
        if f.is_implies():
            a, b = f.args()
            va, vb = self.eval_bool(a), self.eval_bool(b)
            if va is False or vb is True:
                return True
            if va is True:
                return vb
            return None
        if f.is_equals() or f.is_lt() or f.is_le():
            a, b = f.args()
            ai, bi = self._eval_int(a), self._eval_int(b)
            if f.is_equals():
                if ai.lo is not None and ai.hi is not None and bi.lo is not None and bi.hi is not None:
                    if ai.lo == ai.hi == bi.lo == bi.hi:
                        return True
                    if ai.lo > bi.hi or ai.hi < bi.lo:
                        return False
                return None
            if f.is_le():
                if ai.hi is not None and bi.lo is not None and ai.hi <= bi.lo:
                    return True
                if ai.lo is not None and bi.hi is not None and ai.lo > bi.hi:
                    return False
                return None
            if ai.hi is not None and bi.lo is not None and ai.hi < bi.lo:
                return True
            if ai.lo is not None and bi.hi is not None and ai.lo >= bi.hi:
                return False
            return None
        return None

    def _refine_affine_eq(self, a: FNode, b: FNode) -> bool:
        aff_a = _affine(a)
        aff_b = _affine(b)
        if aff_a is None or aff_b is None:
            return False
        ca, ma = aff_a
        cb, mb = aff_b

        const = ca - cb
        terms = dict(ma)
        for s, c in mb.items():
            terms[s] = terms.get(s, 0) - c
            if terms[s] == 0:
                del terms[s]
        if not terms:
            return False

        changed = False
        for sym, coeff in terms.items():
            rest = Interval.const(const)
            for t, c in terms.items():
                if t is sym:
                    continue
                rest = rest.add(self._eval_int(t).scale(c))
            if rest.lo is None or rest.hi is None:
                continue

            lo_num = -rest.hi
            hi_num = -rest.lo
            if coeff < 0:
                coeff = -coeff
                lo_num, hi_num = -hi_num, -lo_num
            lo = _ceil_div(lo_num, coeff)
            hi = _floor_div(hi_num, coeff)
            changed |= self._set_interval(sym, Interval(lo, hi))
        return changed

    def _refine_affine_le(self, a: FNode, b: FNode, strict: bool) -> bool:
        # a <= b  =>  (a-b) <= 0
        # a <  b  =>  (a-b) <= -1
        aff_a = _affine(a)
        aff_b = _affine(b)
        if aff_a is None or aff_b is None:
            return False
        ca, ma = aff_a
        cb, mb = aff_b

        const = ca - cb
        terms = dict(ma)
        for s, c in mb.items():
            terms[s] = terms.get(s, 0) - c
            if terms[s] == 0:
                del terms[s]
        if not terms:
            return False

        target_hi = -1 if strict else 0
        changed = False
        for sym, coeff in terms.items():
            rest = Interval.const(const)
            for t, c in terms.items():
                if t is sym:
                    continue
                rest = rest.add(self._eval_int(t).scale(c))
            if rest.lo is None or rest.hi is None:
                continue

            if coeff > 0:
                # coeff*sym + rest <= target_hi
                # use minimal rest to get strongest upper bound.
                rhs = target_hi - rest.lo
                hi = _floor_div(rhs, coeff)
                changed |= self._set_interval(sym, Interval(INF, hi))
            elif coeff < 0:
                # coeff*sym + rest <= target_hi
                # => sym >= ceil((target_hi - rest.hi)/coeff), coeff < 0
                # normalize to positive denominator.
                den = -coeff
                num = rest.hi - target_hi
                lo = _ceil_div(num, den)
                changed |= self._set_interval(sym, Interval(lo, INF))
        return changed

    def _refine_disjunction_of_equalities(self, f: FNode) -> bool:
        if not f.is_or():
            return False
        sym = None
        vals: list[int] = []
        for d in f.args():
            if not d.is_equals():
                return False
            a, b = d.args()
            if a.is_symbol() and (c := _is_int_const(b)) is not None:
                cur = a
            elif b.is_symbol() and (c := _is_int_const(a)) is not None:
                cur = b
            else:
                return False
            if sym is None:
                sym = cur
            elif sym != cur:
                return False
            vals.append(c)
        if sym is None or not vals:
            return False
        return self._set_interval(sym, Interval(min(vals), max(vals)))

    def _refine_from_mod_zero(self, f: FNode) -> bool:
        """Refine from equalities of the shape (mod e p) = 0."""
        if not f.is_equals():
            return False
        a, b = f.args()
        mod_expr = None
        if a.is_mod() and _is_int_const(b) == 0:
            mod_expr = a
        elif b.is_mod() and _is_int_const(a) == 0:
            mod_expr = b
        if mod_expr is None:
            return False

        inner, modulus = mod_expr.args()
        p = _is_int_const(modulus)
        if p is None or p <= 0:
            return False

        changed = False

        # If there is a unique multiple of p in the current interval of `inner`,
        # we can turn congruence into exact equality for back-propagation.
        inner_iv = self._eval_int(inner)
        uniq = _unique_multiple_in_interval(inner_iv, p)
        if uniq is not None:
            changed |= self._refine_affine_eq(inner, Int(uniq))

        # Prime-field product reasoning:
        #   (u1 * ... * uk) == 0 (mod p)  =>  ui == 0 (mod p) for some i.
        # For affine unit-coefficient factors over canonical symbol ranges, each
        # factor gives a concrete residue candidate; we keep the interval hull.
        if inner.is_times():
            candidates: Dict[FNode, set[int]] = {}
            for factor in inner.args():
                aff = _affine(factor)
                if aff is None:
                    continue
                c0, terms = aff
                if len(terms) != 1:
                    continue
                sym, coeff = next(iter(terms.items()))
                if coeff not in (1, -1):
                    continue
                if not sym.is_symbol() or not sym.get_type().is_int_type():
                    continue
                sym_iv = self.get_interval(sym)
                if not sym_iv.within_0_p(p):
                    continue
                if coeff == 1:
                    cand = (-c0) % p
                else:
                    cand = c0 % p
                candidates.setdefault(sym, set()).add(cand)

            for sym, vals in candidates.items():
                if not vals:
                    continue
                changed |= self._set_interval(sym, Interval(min(vals), max(vals)))

        return changed

    def _refine_atom(self, f: FNode) -> bool:
        changed = self._refine_from_mod_zero(f)
        if f.is_equals():
            a, b = f.args()
            changed |= self._refine_affine_eq(a, b)
            # Symmetric propagation for plain symbol == constant.
            if a.is_symbol() and (c := _is_int_const(b)) is not None:
                changed |= self._set_interval(a, Interval.const(c))
            if b.is_symbol() and (c := _is_int_const(a)) is not None:
                changed |= self._set_interval(b, Interval.const(c))
            return changed
        if f.is_le():
            a, b = f.args()
            return changed | self._refine_affine_le(a, b, strict=False)
        if f.is_lt():
            a, b = f.args()
            return changed | self._refine_affine_le(a, b, strict=True)
        return changed | self._refine_disjunction_of_equalities(f)

    def assume_all(self, formulas: Iterable[FNode], max_iters: int = 32) -> None:
        work: list[tuple[FNode, FNode]] = []
        for f in formulas:
            work.extend((a, f) for a in _flatten_and(f))

        for _ in range(max_iters):
            changed = False
            for atom, origin in work:
                if self.inconsistent:
                    return
                simplified = self.simplify(atom, prune=False)
                local = False
                for a in _flatten_and(simplified):
                    local |= self._refine_atom(a)
                if local:
                    self.strengthening_formulas.add(origin)
                changed |= local
            if not changed:
                break

    def must_retain_formula(self, f: FNode) -> bool:
        """Retain only source assertions that tightened internal bounds."""
        return f in self.strengthening_formulas

    def derived_range_constraints(self, *, only_tightened: bool = True) -> list[FNode]:
        """Materialize inferred intervals as explicit constraints."""
        symbols = self.tightened_symbols if only_tightened else set(self.env.keys())
        out: list[FNode] = []
        for sym in sorted(symbols, key=str):
            iv = self.get_interval(sym)
            if iv.is_bottom():
                out.append(Bool(False))
                continue
            if iv.lo is not None and iv.hi is not None and iv.lo == iv.hi:
                out.append(Equals(sym, Int(iv.lo)))
                continue
            parts = []
            if iv.lo is not None:
                parts.append(LE(Int(iv.lo), sym))
            if iv.hi is not None:
                parts.append(LE(sym, Int(iv.hi)))
            if not parts:
                continue
            out.append(parts[0] if len(parts) == 1 else And(*parts))
        return out

    def simplify(self, f: FNode, *, prune: bool = True) -> FNode:
        memo: Dict[FNode, FNode] = {}

        def go(n: FNode) -> FNode:
            if n in memo:
                return memo[n]

            if prune:
                vb = self.eval_bool(n)
                if vb is True:
                    memo[n] = Bool(True)
                    return memo[n]
                if vb is False:
                    memo[n] = Bool(False)
                    return memo[n]

            if n.is_and():
                args = [go(a) for a in n.args()]
                if prune:
                    out = []
                    for a in args:
                        if _is_bool_const(a) is True:
                            continue
                        if _is_bool_const(a) is False:
                            memo[n] = Bool(False)
                            return memo[n]
                        out.append(a)
                    memo[n] = Bool(True) if not out else And(*out)
                    return memo[n]
                memo[n] = And(*args)
                return memo[n]

            if n.is_or():
                args = [go(a) for a in n.args()]
                if prune:
                    out = []
                    for a in args:
                        if _is_bool_const(a) is False:
                            continue
                        if _is_bool_const(a) is True:
                            memo[n] = Bool(True)
                            return memo[n]
                        out.append(a)
                    memo[n] = Bool(False) if not out else Or(*out)
                    return memo[n]
                memo[n] = Or(*args)
                return memo[n]

            if n.is_not():
                memo[n] = Not(go(n.arg(0)))
                return memo[n]

            if n.is_mod():
                a, m = n.args()
                mv = _is_int_const(m)
                if mv is not None and self._eval_int(a).within_0_p(mv):
                    memo[n] = go(a)
                    return memo[n]
                memo[n] = Mod(go(a), go(m))
                return memo[n]

            if n.is_equals():
                a, b = n.args()
                memo[n] = Equals(go(a), go(b))
                return memo[n]

            if n.is_le():
                a, b = n.args()
                memo[n] = LE(go(a), go(b))
                return memo[n]

            if n.is_lt():
                a, b = n.args()
                memo[n] = LT(go(a), go(b))
                return memo[n]

            memo[n] = n
            return n

        return go(f)


def simplify_intervals(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run fixed-point integer interval propagation on all assertions."""
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        return smt_script

    engine = IntervalICPEngine()
    engine.assume_all(assertions)

    for cmd in smt_script:
        if cmd.name == "assert":
            if engine.inconsistent:
                cmd.args[0] = Bool(False)
            elif engine.must_retain_formula(cmd.args[0]):
                # Keep source-level bound constraints explicit in the simplified output.
                continue
            else:
                cmd.args[0] = engine.simplify(cmd.args[0], prune=True)

    # Preserve information discovered by propagation even when source constraints
    # simplify away under pruning.
    existing_asserts = {cmd.args[0] for cmd in smt_script if cmd.name == "assert"}
    derived_to_insert: list[FNode] = []
    for derived in engine.derived_range_constraints(only_tightened=True):
        if derived not in existing_asserts:
            derived_to_insert.append(derived)
            existing_asserts.add(derived)

    if not derived_to_insert:
        return smt_script

    # Keep derived facts in the assertion block, right before satisfiability checks.
    out = script.SmtLibScript()
    inserted = False
    for cmd in smt_script:
        if not inserted and cmd.name in {"check-sat", "check-sat-assuming"}:
            for derived in derived_to_insert:
                out.add_command(script.SmtLibCommand(name="assert", args=[derived]))
            inserted = True
        out.add_command(cmd)

    if not inserted:
        for derived in derived_to_insert:
            out.add_command(script.SmtLibCommand(name="assert", args=[derived]))

    return out
