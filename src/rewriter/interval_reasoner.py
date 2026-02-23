from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Optional

from pysmt import operators

from ..smt.utils import ARGS, And, Bool, Equals, FNode, Implies, Int, Mod, Not, Or


INF = None  # unbounded side marker


@dataclass(frozen=True)
class IntInterval:
    lo: Optional[int]
    hi: Optional[int]

    @staticmethod
    def top() -> "IntInterval":
        return IntInterval(INF, INF)

    @staticmethod
    def const(v: int) -> "IntInterval":
        return IntInterval(v, v)

    def is_bottom(self) -> bool:
        return self.lo is not None and self.hi is not None and self.lo > self.hi

    def intersect(self, other: "IntInterval") -> "IntInterval":
        lo = other.lo if self.lo is None else (self.lo if other.lo is None else max(self.lo, other.lo))
        hi = other.hi if self.hi is None else (self.hi if other.hi is None else min(self.hi, other.hi))
        return IntInterval(lo, hi)

    def add(self, other: "IntInterval") -> "IntInterval":
        lo = None if self.lo is None or other.lo is None else self.lo + other.lo
        hi = None if self.hi is None or other.hi is None else self.hi + other.hi
        return IntInterval(lo, hi)

    def neg(self) -> "IntInterval":
        lo = None if self.hi is None else -self.hi
        hi = None if self.lo is None else -self.lo
        return IntInterval(lo, hi)

    def sub(self, other: "IntInterval") -> "IntInterval":
        return self.add(other.neg())

    def mul(self, other: "IntInterval") -> "IntInterval":
        if self.lo is None or self.hi is None or other.lo is None or other.hi is None:
            return IntInterval.top()
        vals = [
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        ]
        return IntInterval(min(vals), max(vals))

    def within_0_p(self, p: int) -> bool:
        return self.lo is not None and self.hi is not None and 0 <= self.lo and self.hi < p

    def within_open_pm_p(self, p: int) -> bool:
        return self.lo is not None and self.hi is not None and (-p) < self.lo and self.hi < p


def _is_int_const(n: FNode) -> Optional[int]:
    # Do not call is_int_constant() on arbitrary nodes: pySMT can raise on array values.
    if n.node_type() == operators.INT_CONSTANT:
        return int(n.constant_value())
    return None


def _is_bool_const(n: FNode) -> Optional[bool]:
    if n.node_type() == operators.BOOL_CONSTANT:
        return bool(n.constant_value())
    return None


def _is_mod_p(n: FNode, p: int) -> Optional[FNode]:
    if not n.is_mod():
        return None
    a, m = n.args()
    if _is_int_const(m) == p:
        return a
    return None


def _flatten_and(f: FNode) -> Iterable[FNode]:
    if f.is_and():
        for a in f.args():
            yield from _flatten_and(a)
    else:
        yield f


class IntervalReasoner:
    """Interval propagation over pySMT Int formulas under finite-field modulus p."""

    def __init__(self, modulus: Optional[int] = None):
        self.p = int(ARGS().field_type.value if modulus is None else modulus)
        self.env: Dict[FNode, IntInterval] = {}
        self.used_formulas: set[FNode] = set()
        self._cache: Dict[FNode, IntInterval] = {}

    def _default(self, sym: FNode) -> IntInterval:
        return IntInterval(0, self.p - 1)

    def get_interval(self, sym: FNode) -> IntInterval:
        if sym in self.env:
            return self.env[sym]
        if sym.is_symbol() and sym.get_type().is_int_type():
            self.env[sym] = self._default(sym)
            return self.env[sym]
        return IntInterval.top()

    def _set_interval(self, sym: FNode, new_i: IntInterval) -> bool:
        old = self.get_interval(sym)
        merged = old.intersect(new_i)
        if merged == old:
            return False
        self.env[sym] = merged
        self._cache.clear()
        return True

    def _eval_int(self, e: FNode) -> IntInterval:
        if e in self._cache:
            return self._cache[e]

        if (c := _is_int_const(e)) is not None:
            r = IntInterval.const(c)
        elif e.is_symbol():
            r = self.get_interval(e)
        elif e.is_plus():
            acc = IntInterval.const(0)
            for a in e.args():
                acc = acc.add(self._eval_int(a))
            r = acc
        elif e.is_minus():
            a, b = e.args()
            r = self._eval_int(a).sub(self._eval_int(b))
        elif e.is_times():
            acc = IntInterval.const(1)
            for a in e.args():
                acc = acc.mul(self._eval_int(a))
            r = acc
        elif e.is_mod():
            a, m = e.args()
            mv = _is_int_const(m)
            if mv is not None and mv > 0:
                ai = self._eval_int(a)
                if ai.within_0_p(mv):
                    r = ai
                else:
                    r = IntInterval(0, mv - 1)
            else:
                r = IntInterval.top()
        else:
            r = IntInterval.top()

        self._cache[e] = r
        return r

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
            ai = self._eval_int(a)
            bi = self._eval_int(b)
            if f.is_equals():
                if ai.lo is not None and ai.hi is not None and bi.lo is not None and bi.hi is not None:
                    if ai.lo == ai.hi == bi.lo == bi.hi:
                        return True
                    if ai.lo > bi.hi or ai.hi < bi.lo:
                        return False
                return None
            if f.is_lt():
                if ai.hi is not None and bi.lo is not None and ai.hi < bi.lo:
                    return True
                if ai.lo is not None and bi.hi is not None and ai.lo >= bi.hi:
                    return False
                return None
            if f.is_le():
                if ai.hi is not None and bi.lo is not None and ai.hi <= bi.lo:
                    return True
                if ai.lo is not None and bi.hi is not None and ai.lo > bi.hi:
                    return False
                return None
        return None

    def _refine_from_ineq(self, f: FNode) -> bool:
        if not (f.is_lt() or f.is_le()):
            return False
        a, b = f.args()
        strict = f.is_lt()
        am = _is_mod_p(a, self.p)
        bm = _is_mod_p(b, self.p)
        if am is not None:
            a = am
        if bm is not None:
            b = bm

        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            return self._set_interval(a, IntInterval(INF, c - 1 if strict else c))
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            return self._set_interval(b, IntInterval(c + 1 if strict else c, INF))
        return False

    def _refine_from_eq(self, f: FNode) -> bool:
        if not f.is_equals():
            return False
        a, b = f.args()
        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            return self._set_interval(a, IntInterval.const(c))
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            return self._set_interval(b, IntInterval.const(c))

        # Mod(sym,p) == c and sym already canonical -> sym == c
        if (x := _is_mod_p(a, self.p)) is not None and (c := _is_int_const(b)) is not None:
            if self._eval_int(x).within_0_p(self.p) and x.is_symbol():
                return self._set_interval(x, IntInterval.const(c))
        if (x := _is_mod_p(b, self.p)) is not None and (c := _is_int_const(a)) is not None:
            if self._eval_int(x).within_0_p(self.p) and x.is_symbol():
                return self._set_interval(x, IntInterval.const(c))
        return False

    def _refine_from_or_equalities(self, f: FNode) -> bool:
        if not f.is_or():
            return False
        sym = None
        vals: list[int] = []
        for d in f.args():
            if not d.is_equals():
                return False
            a, b = d.args()
            if a.is_symbol() and (c := _is_int_const(b)) is not None:
                cur_sym = a
            elif b.is_symbol() and (c := _is_int_const(a)) is not None:
                cur_sym = b
            else:
                return False
            if sym is None:
                sym = cur_sym
            elif sym != cur_sym:
                return False
            vals.append(c)
        if sym is None or not vals:
            return False
        return self._set_interval(sym, IntInterval(min(vals), max(vals)))

    def assume_all(self, assumptions: Iterable[FNode], max_iters: int = 6) -> None:
        work = []
        for a in assumptions:
            work.extend(list(_flatten_and(a)))

        for _ in range(max_iters):
            changed = False
            for f in work:
                local = False
                local |= self._refine_from_ineq(f)
                local |= self._refine_from_eq(f)
                local |= self._refine_from_or_equalities(f)
                if local:
                    self.used_formulas.add(f)
                changed |= local
            if not changed:
                break

    def must_retain_formula(self, f: FNode) -> bool:
        """Return True for constraints that must not be pruned away.

        Even if a formula is currently implied by our abstract state, constraints
        that explicitly encode integer-domain field bounds (e.g. 0 <= x, x < p)
        must remain in the final SMT encoding.
        """
        if f.is_and():
            return any(self.must_retain_formula(a) for a in f.args())
        if not (f.is_le() or f.is_lt() or f.is_equals()):
            return False

        a, b = f.args()
        ac = _is_int_const(a)
        bc = _is_int_const(b)

        # symbol-side checks (we only retain direct symbol guards here)
        if f.is_le():
            # 0 <= x  /  x <= p / x <= p-1
            if ac == 0 and b.is_symbol():
                return True
            if bc in (self.p, self.p - 1) and a.is_symbol():
                return True
        elif f.is_lt():
            # x < p / x < p+1 (occasionally emitted by normalizations)
            if bc in (self.p, self.p + 1) and a.is_symbol():
                return True
        else:  # equals
            # Keep explicit pinning to 0 or p in integer encoding.
            if ac in (0, self.p) and b.is_symbol():
                return True
            if bc in (0, self.p) and a.is_symbol():
                return True

        return False

    def simplify(self, f: FNode, *, prune: bool = True, freeze: Optional[set[FNode]] = None) -> FNode:
        if freeze and f in freeze:
            return f
        memo: Dict[FNode, FNode] = {}

        def go(n: FNode) -> FNode:
            if n in memo:
                return memo[n]
            if freeze and n in freeze:
                memo[n] = n
                return n

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

            if n.is_implies():
                a, b = n.args()
                sa, sb = go(a), go(b)
                memo[n] = Implies(sa, sb)
                return memo[n]

            if n.is_not():
                memo[n] = Not(go(n.arg(0)))
                return memo[n]

            if n.is_mod():
                a, m = n.args()
                mv = _is_int_const(m)
                if mv is not None and self._eval_int(a).within_0_p(mv):
                    memo[n] = a
                    return memo[n]
                memo[n] = Mod(go(a), go(m))
                return memo[n]

            if n.is_equals():
                a, b = n.args()
                if (x := _is_mod_p(a, self.p)) is not None and _is_int_const(b) == 0:
                    if self._eval_int(x).within_open_pm_p(self.p):
                        memo[n] = Equals(x, Int(0))
                        return memo[n]
                if (x := _is_mod_p(b, self.p)) is not None and _is_int_const(a) == 0:
                    if self._eval_int(x).within_open_pm_p(self.p):
                        memo[n] = Equals(x, Int(0))
                        return memo[n]
                memo[n] = Equals(go(a), go(b))
                return memo[n]

            memo[n] = n
            return n

        return go(f)

