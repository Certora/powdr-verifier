from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Hashable, Iterable, Iterator, Mapping, Optional, TypeVar

from ...smt.utils import *

V = TypeVar("V", bound=Hashable)


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
    
    def __repr__(self) -> str:
        lo = "(-oo" if self.lo is None else f"[{self.lo}"
        hi = "oo)" if self.hi is None else f"{self.hi}]"
        return f"{lo},{hi}"

    def is_bottom(self) -> bool:
        return self.lo is not None and self.hi is not None and self.lo > self.hi

    def intersects(self, other: "IntInterval") -> bool:
        return not self.intersect(other).is_bottom()

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
        vals = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return IntInterval(min(vals), max(vals))

    def scale(self, k: int) -> "IntInterval":
        if k == 0:
            return IntInterval.const(0)
        lo = None if self.lo is None else self.lo * k
        hi = None if self.hi is None else self.hi * k
        if k > 0:
            return IntInterval(lo, hi)
        return IntInterval(hi, lo)

    def within_0_p(self, p: int) -> bool:
        return self.lo is not None and self.hi is not None and 0 <= self.lo and self.hi < p

    def within_open_pm_p(self, p: int) -> bool:
        return self.lo is not None and self.hi is not None and (-p) < self.lo and self.hi < p

    def contains(self, v: int) -> bool:
        lo_ok = self.lo is None or self.lo <= v
        hi_ok = self.hi is None or v <= self.hi
        return lo_ok and hi_ok

    def to_constraints(self, sym: FNode) -> Iterator[FNode]:
        """Yield at most one integer-theory constraint for ``sym``; empty if unbounded (no finite guard)."""
        if self.is_bottom():
            yield Bool(False)
        elif self.lo is None and self.hi is None:
            pass
        elif self.lo is not None and self.hi is not None and self.lo == self.hi:
            yield Equals(sym, Int(self.lo))
        else:
            if self.lo is not None:
                yield Int(self.lo) <= sym
            if self.hi is not None:
                yield sym <= Int(self.hi)


def _lo_key(v: Optional[int]) -> float:
    return float("-inf") if v is None else float(v)


def _hi_key(v: Optional[int]) -> float:
    return float("inf") if v is None else float(v)


def _mergeable(a: IntInterval, b: IntInterval) -> bool:
    if a.is_bottom() or b.is_bottom():
        return False
    if a.hi is None or b.lo is None:
        return True
    return a.hi >= b.lo


def _merge_interval(a: IntInterval, b: IntInterval) -> IntInterval:
    lo = a.lo if _lo_key(a.lo) <= _lo_key(b.lo) else b.lo
    if a.hi is None or b.hi is None:
        hi = None
    else:
        hi = max(a.hi, b.hi)
    return IntInterval(lo, hi)


def _normalize_intervals(intervals: Iterable[IntInterval]) -> tuple[IntInterval, ...]:
    items = [iv for iv in intervals if not iv.is_bottom()]
    if not items:
        return ()
    items.sort(key=lambda iv: (_lo_key(iv.lo), _hi_key(iv.hi)))
    out: list[IntInterval] = [items[0]]
    for iv in items[1:]:
        last = out[-1]
        if _mergeable(last, iv):
            out[-1] = _merge_interval(last, iv)
        else:
            out.append(iv)
    return tuple(out)


@dataclass(frozen=True)
class IntDomain:
    parts: tuple[IntInterval, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "parts", _normalize_intervals(self.parts))

    @staticmethod
    def bottom() -> "IntDomain":
        return IntDomain(())

    @staticmethod
    def top() -> "IntDomain":
        return IntDomain((IntInterval.top(),))

    @staticmethod
    def const(v: int) -> "IntDomain":
        return IntDomain((IntInterval.const(v),))

    @staticmethod
    def from_interval(iv: IntInterval) -> "IntDomain":
        return IntDomain((iv,))

    @staticmethod
    def from_intervals(intervals: Iterable[IntInterval]) -> "IntDomain":
        return IntDomain(tuple(intervals))
    
    def __repr__(self) -> str:
        return "|".join(str(iv) for iv in self.parts)

    def is_bottom(self) -> bool:
        return len(self.parts) == 0

    def is_top(self) -> bool:
        return len(self.parts) == 1 and self.parts[0] == IntInterval.top()

    def hull(self) -> IntInterval:
        if self.is_bottom():
            return IntInterval(1, 0)
        return IntInterval(self.parts[0].lo, self.parts[-1].hi)

    def intersect(self, other: "IntDomain") -> "IntDomain":
        if self.is_bottom() or other.is_bottom():
            return IntDomain.bottom()
        i = 0
        j = 0
        out: list[IntInterval] = []
        a = self.parts
        b = other.parts
        while i < len(a) and j < len(b):
            inter = a[i].intersect(b[j])
            if not inter.is_bottom():
                out.append(inter)
            if _hi_key(a[i].hi) <= _hi_key(b[j].hi):
                i += 1
            else:
                j += 1
        return IntDomain.from_intervals(out)

    def union(self, other: "IntDomain") -> "IntDomain":
        if self.is_bottom():
            return other
        if other.is_bottom():
            return self
        return IntDomain.from_intervals(self.parts + other.parts)

    def add(self, other: "IntDomain") -> "IntDomain":
        if self.is_bottom() or other.is_bottom():
            return IntDomain.bottom()
        out: list[IntInterval] = []
        for a in self.parts:
            for b in other.parts:
                out.append(a.add(b))
        return IntDomain.from_intervals(out)

    def neg(self) -> "IntDomain":
        if self.is_bottom():
            return IntDomain.bottom()
        return IntDomain.from_intervals(iv.neg() for iv in self.parts)

    def sub(self, other: "IntDomain") -> "IntDomain":
        return self.add(other.neg())

    def mul(self, other: "IntDomain") -> "IntDomain":
        if self.is_bottom() or other.is_bottom():
            return IntDomain.bottom()
        out: list[IntInterval] = []
        for a in self.parts:
            for b in other.parts:
                out.append(a.mul(b))
        return IntDomain.from_intervals(out)

    def scale(self, k: int) -> "IntDomain":
        if self.is_bottom():
            return IntDomain.bottom()
        return IntDomain.from_intervals(iv.scale(k) for iv in self.parts)

    def within_0_p(self, p: int) -> bool:
        return not self.is_bottom() and all(iv.within_0_p(p) for iv in self.parts)

    def within_open_pm_p(self, p: int) -> bool:
        return not self.is_bottom() and all(iv.within_open_pm_p(p) for iv in self.parts)

    def contains(self, v: int) -> bool:
        return any(iv.contains(v) for iv in self.parts)

    def singleton_value(self) -> Optional[int]:
        if len(self.parts) != 1:
            return None
        iv = self.parts[0]
        if iv.lo is None or iv.hi is None or iv.lo != iv.hi:
            return None
        return iv.lo

    def to_constraints(self, sym: FNode) -> FNode:
        """Yield at most one formula: a disjunction of per-interval guards; empty if the domain is unconstrained."""
        if self.is_bottom():
            return Bool(False)
        disjuncts: list[FNode] = [
            And(*list(iv.to_constraints(sym))) for iv in self.parts
        ]
        match len(disjuncts):
            case 0: return TRUE()
            case 1: return disjuncts[0]
            case _: return Or(*disjuncts)


def _fmt_int_interval(iv: IntInterval) -> str:
    lo = "-inf" if iv.lo is None else str(iv.lo)
    hi = "+inf" if iv.hi is None else str(iv.hi)
    return f"[{lo},{hi}]"


def _fmt_int_domain(dom: IntDomain) -> str:
    if dom.is_bottom():
        return "<empty>"
    if dom.is_top():
        return "top"
    return " | ".join(_fmt_int_interval(iv) for iv in dom.parts)


def _omit_from_var_domains_str(dom: IntDomain) -> bool:
    """True if ``dom`` is unconstrained ℤ or the full field range [0, p-1] / [0, p]."""
    if dom.is_top():
        return True
    from ...utils.args import ARGS

    p = int(ARGS().field_type.value)
    if dom == IntDomain.from_interval(IntInterval(0, p - 1)):
        return True
    if dom == IntDomain.from_interval(IntInterval(0, p)):
        return True
    return False


class IntVarDomains(Generic[V]):
    """Sparse map from variables to `IntDomain` (Cartesian product semantics).

    Mutable: the internal mapping is a plain ``dict`` (copied on construction from inputs).

    A key absent from the mapping means that variable is unconstrained (`IntDomain.top()`).

    `intersect` is the meet (narrowing): per-variable domain intersection, with missing
    variables treated as top on both sides.

    `union` is the join (over-approximation of set union of concrete stores): per-variable
    exact `IntDomain.union` followed by `IntDomain.hull` (interval convex hull), with
    missing variables treated as top so a one-sided refinement widens to top on merge.
    """

    __slots__ = ("_bottom", "_m")

    def __init__(self, mapping: Mapping[V, IntDomain] = {}, *, _bottom: bool = False) -> None:
        self._bottom = _bottom or any(dom.is_bottom() for dom in mapping.values())
        self._m: dict[V, IntDomain] = {}
        if not self._bottom and mapping is not None:
            self._m = {k: dom for k, dom in mapping.items() if not dom.is_top()}

    @staticmethod
    def bottom() -> "IntVarDomains":
        return IntVarDomains(_bottom=True)

    @staticmethod
    def top() -> "IntVarDomains[V]":
        return IntVarDomains()

    @staticmethod
    def from_mapping(mapping: Mapping[V, IntDomain]) -> "IntVarDomains[V]":
        return IntVarDomains(mapping)

    @staticmethod
    def singleton(var: V, dom: IntDomain) -> "IntVarDomains[V]":
        return IntVarDomains({var: dom})

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, IntVarDomains):
            return NotImplemented
        return self._bottom == other._bottom and self._m == other._m

    def __repr__(self) -> str:
        if self.is_bottom():
            return "IntVarDomains(bottom)"
        if self.is_top():
            return "IntVarDomains(top)"
        pairs = [
            (sym, dom)
            for sym, dom in sorted(self._m.items(), key=lambda kv: str(kv[0]))
            if not _omit_from_var_domains_str(dom)
        ]
        if not pairs:
            return "IntVarDomains({})"
        inner = ", ".join(f"{sym} -> {_fmt_int_domain(dom)}" for sym, dom in pairs)
        return f"IntVarDomains({{{inner}}})"

    def is_bottom(self) -> bool:
        return self._bottom

    def is_top(self) -> bool:
        return not self._bottom and len(self._m) == 0

    def __contains__(self, var: V) -> bool:
        if self._bottom:
            return False
        return var in self._m
    
    def __getitem__(self, var: V) -> IntDomain:
        if self._bottom:
            return IntDomain.bottom()
        return self._m.get(var, IntDomain.top())
    
    def __setitem__(self, var: V, dom: IntDomain) -> None:
        if self._bottom:
            return
        if dom.is_bottom():
            self._bottom = True
            self._m = {}
            return
        if dom.is_top():
            self._m.pop(var, None)
            return
        self._m[var] = dom

    def get(self, var: V) -> IntDomain:
        if self._bottom:
            return IntDomain.bottom()
        return self._m.get(var, IntDomain.top())

    def keys(self) -> Iterable[V]:
        if self._bottom:
            return ()
        return self._m.keys()

    def items(self) -> Iterable[tuple[V, IntDomain]]:
        if self._bottom:
            return ()
        return self._m.items()

    def to_dict(self) -> dict[V, IntDomain]:
        if self._bottom:
            return {}
        return dict(self._m)

    def to_constraints(self, vars: frozenset[FNode] = None) -> Iterator[FNode]:
        """Yield one guard per stored binding (conjoin for a full guard). Keys must be integer symbols."""
        if self.is_bottom():
            yield Bool(False)
            return
        for sym, dom in self.items():
            if vars is not None and sym not in vars:
                continue
            if not _omit_from_var_domains_str(dom):
                yield dom.to_constraints(sym)

    def intersect(self, other: "IntVarDomains[V]") -> "IntVarDomains[V]":
        if self._bottom or other._bottom:
            return IntVarDomains.bottom()
        out: dict[V, IntDomain] = {}
        for k in self._m.keys() | other._m.keys():
            if k not in self:
                out[k] = other.get(k)
            elif k not in other:
                out[k] = self.get(k)
            else:
                inter = self.get(k).intersect(other.get(k))
                if inter.is_bottom():
                    return IntVarDomains.bottom()
                if not inter.is_top():
                    out[k] = inter
        return IntVarDomains(out)

    def union(self, other: "IntVarDomains[V]") -> "IntVarDomains[V]":
        """Join: over-approximate union of two abstract stores (per-variable hull after union)."""
        if self._bottom:
            return IntVarDomains(dict(other._m), _bottom=other._bottom)
        if other._bottom:
            return IntVarDomains(dict(self._m))
        out: dict[V, IntDomain] = {}
        for k in self._m.keys() | other._m.keys():
            combined = self.get(k).union(other.get(k))
            joined = IntDomain.from_interval(combined.hull())
            if not joined.is_top():
                out[k] = joined
        return IntVarDomains(out)
