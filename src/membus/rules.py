"""Extraction rules: dump → facts. Each rule states its full side conditions.

The rules recover integer facts from field constraints. The recurring danger
is the field/integer gap: a constraint holds **mod p**, and reading it as an
integer statement needs a *window argument* — bounds on every participating
column tight enough that the field equation has exactly the claimed integer
solutions. Every rule here performs its window argument explicitly, from
:class:`~.facts.Bound` facts and the named :class:`~.facts.Assumption`s; a
rule that cannot justify its window **declines** (returns nothing) rather
than assume the common case.

Rules (names follow the R0/R1/R2 scheme of the busat prototype):

- **R0 → Bound.** A range-check bus arg bounds *its value*; only a bare
  column arg bounds a column. A scaled arg ``c·col`` with ``s = c⁻¹ mod p``
  and ``s·2^bits < p`` bounds ``col`` to ``[0, s·2^bits)``. Compound
  multi-column args bound **no** column (marking their columns nonneg was
  review finding 5). Memory-bus **recv** data args are bytes by
  ``Assumption.MEMBUS_BYTE`` (recv only — writes are the circuit's burden).
- **R1 → Gap.** A constraint ``a − b + c = 0`` over two from_state columns
  reads as the integer gap ``a = b − c`` under ``TS_BOUND`` (window < p holds
  for any canonical constant).
- **R2 → RecvUpper,** constraint form. ``fs − pv − Σ m_i·l_i + c = 0`` with
  ``m_i > 0`` and every limb bounded: window check, then ``pv ≤ fs + c``.
- **R2 → RecvUpper,** range-check form (post-`inlining`). The LessThan
  gadget's top limb survives only as a range-checked *scaled* combination
  ``±s·(fs − pv − Σ m_i·l_i + c)``. The residue being in ``[0, 2^bits)``
  admits the integer solutions ``k ≡ (±s)⁻¹·r (mod p)`` inside the window; we
  **enumerate** them and require every one to be ``≥ 0`` (the conclusion needs
  only ``k ≥ 0``, and negative solutions are exactly the unsound cases —
  review finding 3: acceptance must depend on the *sign* of the scale factor,
  which the divisibility test alone cannot see).
- **Affine gadget → AffineDef.** ``G·H = 0`` with ``H = G + δ``: solving
  ``G = 0`` for a limb is justified only if (i) the integer root of the chosen
  factor is unique in its window, and (ii) the **other factor's** roots inside
  the window are refuted (only ``k = 0`` may remain — review finding 4: the
  gadget has two roots and the code must prove the witness cannot sit on the
  other one).
- **Kind → EffKind.** Multiplicity ↦ send/recv/disabled: constant ±1/0, or —
  under ``--assume-is-valid`` — a linear combination of ``is_valid`` columns
  evaluated at ``is_valid = 1`` (``IS_VALID_BOOLEAN``).
"""
from __future__ import annotations

import functools
import math
from typing import Any

from src.lens.loader import machine_of
from src.lens.normalize import BABYBEAR_PRIME

from . import naming
from .busmodel import (
    BITWISE,
    MEMORY,
    TUPLE_RANGE,
    VAR_RANGE,
    MemRow,
    bus_ordinal_of_mem,
    memory_rows,
    range_bus_rows,
)
from .facts import TS_MAX, AffineDef, Assumption, Bound, EffKind, Fact, Gap, RecvUpper, Src
from .linform import LinForm, linform, product

P = BABYBEAR_PRIME

# Residue-enumeration cap for the range-check R2 form: 2^bits SMT-free loop
# iterations per candidate row. Corpus widths are ≤ 12 bits.
_MAX_ENUM_BITS = 16


def _bits_of(arg: Any) -> int | None:
    """The bit-width arg of a VariableRangeChecker row, if constant."""
    if isinstance(arg, str) and arg.isdigit():
        arg = int(arg)
    return arg if isinstance(arg, int) and 0 <= arg < 31 else None


class Analysis:
    """All facts extracted from one dump. Owns the caches (nothing is stashed
    inside the input JSON), and is the single entry point the deduction layer
    (solve / align / extract) goes through."""

    def __init__(self, data: Any, mem_id: int = MEMORY, assume_is_valid: bool = True):
        self.machine = machine_of(data)
        self.mem_id = mem_id
        self.assume_is_valid = assume_is_valid
        self.mem = memory_rows(data, mem_id)
        self._mem_bus_ordinal = bus_ordinal_of_mem(data, mem_id)

    def mem_src(self, row: MemRow) -> Src:
        return Src("bus", self._mem_bus_ordinal[row.ordinal])

    # -- Kind ---------------------------------------------------------------

    @functools.cached_property
    def kinds(self) -> dict[int, EffKind | None]:
        """Membus ordinal → EffKind fact, or None when the multiplicity does
        not resolve (genuinely symbolic — pre-`solver` flag muxes)."""
        out: dict[int, EffKind | None] = {}
        for row in self.mem:
            out[row.ordinal] = self._kind(row)
        return out

    def _kind(self, row: MemRow) -> EffKind | None:
        lf = linform(row.mult)
        if lf is None:
            return None
        src = (self.mem_src(row),)
        if lf.is_const:
            v = lf.const % P
            kind = {1: "send", P - 1: "recv", 0: "disabled"}.get(v)
            return EffKind(row.ordinal, kind, sources=src) if kind else None
        if self.assume_is_valid and all(naming.is_valid_col(c) for c in lf.columns):
            v = (lf.const + sum(v for _, v in lf.items())) % P   # is_valid := 1
            kind = {1: "send", P - 1: "recv", 0: "disabled"}.get(v)
            if kind:
                return EffKind(row.ordinal, kind, sources=src,
                               assumptions=frozenset({Assumption.IS_VALID_BOOLEAN,
                                                      Assumption.NAMING}))
        return None

    # -- R0: bounds ---------------------------------------------------------

    @functools.cached_property
    def bounds(self) -> dict[str, Bound]:
        """Column → tightest known Bound fact."""
        out: dict[str, Bound] = {}

        def put(fact: Bound) -> None:
            cur = out.get(fact.col)
            if cur is None:
                out[fact.col] = fact
            elif fact.hi is not None and (cur.hi is None or fact.hi < cur.hi):
                out[fact.col] = fact

        for idx, bid, args in range_bus_rows(self.machine):
            src = (Src("bus", idx),)
            if bid == VAR_RANGE and len(args) >= 2:
                bits = _bits_of(args[1])
                if bits is None:
                    continue
                val = args[0]
                if isinstance(val, str):
                    put(Bound(val, 0, 1 << bits, sources=src))
                elif (isinstance(val, list) and len(val) == 3 and val[1] == "*"
                      and isinstance(val[0], int) and isinstance(val[2], str)):
                    try:
                        s = pow(val[0] % P, -1, P)
                    except ValueError:
                        continue
                    if s * (1 << bits) < P:      # no wrap ⟹ sound scaled bound
                        put(Bound(val[2], 0, s * (1 << bits), sources=src))
            elif bid == BITWISE:
                for a in args[:2]:
                    if isinstance(a, str):
                        put(Bound(a, 0, 1 << 8, sources=src))
            elif bid == TUPLE_RANGE:
                for a in args:
                    if isinstance(a, str):
                        put(Bound(a, 0, None, sources=src))

        for row in self.mem:                     # membus-byte: recv data only
            k = self.kinds.get(row.ordinal)
            if k is None or k.kind != "recv":
                continue
            for a in row.data:
                if isinstance(a, str):
                    put(Bound(a, 0, 1 << 8, sources=(self.mem_src(row),),
                              premises=(k,) if k.assumptions else (),
                              assumptions=frozenset({Assumption.MEMBUS_BYTE})))
        return out

    def _hi(self, col: str) -> int | None:
        b = self.bounds.get(col)
        return b.hi if b is not None else None

    def _ts_window(self, terms: list[tuple[str, int]], const: int,
                   ) -> tuple[int, int, tuple[Fact, ...]] | None:
        """Integer window ``[lo, hi]`` of ``Σ coeff·col + const`` where ts
        columns use TS_BOUND and every other column needs a Bound with a
        known width. None if some column is unbounded."""
        lo = hi = const
        prem: list[Fact] = []
        for col, c in terms:
            if naming.is_ts(col):
                top = TS_MAX - 1
            else:
                b = self.bounds.get(col)
                if b is None or b.hi is None or b.lo < 0:
                    return None
                top = b.hi - 1
                prem.append(b)
            lo += min(0, c * top)
            hi += max(0, c * top)
        return lo, hi, tuple(prem)

    # -- R1: gaps -----------------------------------------------------------

    @functools.cached_property
    def gaps(self) -> list[Gap]:
        out = []
        for idx, con in enumerate(self.machine.get("constraints", [])):
            lf = linform(con)
            if lf is None or len(lf.coeffs) != 2:
                continue
            (a, ca), (b, cb) = lf.coeffs
            if not (naming.is_fs(a) and naming.is_fs(b)) or {ca, cb} != {1, -1}:
                continue
            pos, neg = (a, b) if ca == 1 else (b, a)
            gap = -lf.const                        # pos = neg + gap
            if gap == 0 or abs(gap) >= TS_MAX:     # window/usability guard
                continue
            later, earlier = (pos, neg) if gap > 0 else (neg, pos)
            out.append(Gap(later, earlier, abs(gap), sources=(Src("constraint", idx),),
                           assumptions=frozenset({Assumption.TS_BOUND, Assumption.NAMING})))
        return out

    # -- R2: recv bounds ----------------------------------------------------

    @functools.cached_property
    def recv_uppers(self) -> dict[str, list[RecvUpper]]:
        """prev_timestamp column → all RecvUpper facts about it (consumers
        must intersect, i.e. use the minimum threshold)."""
        out: dict[str, list[RecvUpper]] = {}
        for f in self._recv_upper_constraints() + self._recv_upper_range_checks():
            out.setdefault(f.pv, []).append(f)
        return out

    def _split_ts(self, lf: LinForm) -> tuple[list, list, list]:
        fs = [(c, v) for c, v in lf.items() if naming.is_fs(c)]
        pv = [(c, v) for c, v in lf.items() if naming.is_prev(c)]
        rest = [(c, v) for c, v in lf.items() if not naming.is_ts(c)]
        return fs, pv, rest

    def _recv_upper_constraints(self) -> list[RecvUpper]:
        out = []
        for idx, con in enumerate(self.machine.get("constraints", [])):
            lf = linform(con)
            if lf is None:
                continue
            fs, pv, rest = self._split_ts(lf)
            if len(fs) != 1 or len(pv) != 1 or fs[0][1] != 1 or pv[0][1] != -1:
                continue
            if any(v >= 0 for _, v in rest):
                continue
            win = self._ts_window(list(lf.coeffs), lf.const)
            if win is None:
                continue
            lo, hi, prem = win
            if not (lo > -P and hi < P):           # k ≡ 0 (mod p) ⟹ k = 0
                continue
            out.append(RecvUpper(
                pv[0][0], fs[0][0], lf.const,
                sources=(Src("constraint", idx),), premises=prem,
                assumptions=frozenset({Assumption.TS_BOUND, Assumption.NAMING})))
        return out

    def _recv_upper_range_checks(self) -> list[RecvUpper]:
        out = []
        for idx, bid, args in range_bus_rows(self.machine):
            if bid != VAR_RANGE or len(args) < 2:
                continue
            bits = _bits_of(args[1])
            lf = linform(args[0])
            if bits is None or bits > _MAX_ENUM_BITS or lf is None:
                continue
            fs, pv, rest = self._split_ts(lf)
            if len(fs) != 1 or len(pv) != 1:
                continue
            cf, cp = fs[0][1], pv[0][1]
            s = abs(cf)
            if cf != -cp or s in (0, 1):
                continue
            if any(v % s for _, v in lf.items()) or lf.const % s:
                continue
            sign = 1 if cf > 0 else -1
            nrest = [(c, sign * v // s) for c, v in rest]
            nconst = sign * lf.const // s
            if any(v >= 0 for _, v in nrest):
                continue
            # window of k = fs − pv + Σ v·col + nconst
            win = self._ts_window([(fs[0][0], 1), (pv[0][0], -1), *nrest], nconst)
            if win is None:
                continue
            lo, hi, prem = win
            if not (lo > -P and hi < P):
                continue                    # candidate set below assumes window ⊂ (−p, p)
            # enumerate the integer solutions the residue fact admits:
            # arg = sign·s·k, residue(arg) = r ∈ [0, 2^bits) ⟹ k ≡ (sign·s)⁻¹·r.
            # The conclusion pv ≤ fs + nconst follows iff every admitted k ≥ 0.
            inv = pow((sign * s) % P, -1, P)
            sound = True
            for r in range(1 << bits):
                k0 = inv * r % P
                for cand in (k0, k0 - P):
                    if lo <= cand <= hi and cand < 0:
                        sound = False
                        break
                if not sound:
                    break
            if not sound:
                continue
            out.append(RecvUpper(
                pv[0][0], fs[0][0], nconst,
                sources=(Src("bus", idx),), premises=prem,
                assumptions=frozenset({Assumption.TS_BOUND, Assumption.NAMING})))
        return out

    # -- Affine byte-decomposition gadget ------------------------------------

    @functools.cached_property
    def _products(self) -> dict[str, list[tuple[int, Any]]]:
        """Column → [(constraint idx, product constraint)] mentioning it."""
        idx: dict[str, list[tuple[int, Any]]] = {}
        for i, c in enumerate(self.machine.get("constraints", [])):
            pr = product(c)
            if pr is None:
                continue
            for col in {k for k, _ in pr.left.items()} | {k for k, _ in pr.right.items()}:
                idx.setdefault(col, []).append((i, pr))
        return idx

    @functools.lru_cache(maxsize=None)
    def affine(self, col: str) -> AffineDef | None:
        """The affine definition of ``col`` from a decomposition gadget, with
        both the chosen-root window and the other-root refutation checked."""
        b_col = self.bounds.get(col)
        if b_col is None or b_col.hi is None:
            return None
        for idx, pr in self._products.get(col, []):
            if pr.left.coeffs != pr.right.coeffs:      # factors must differ by a const
                continue
            for factor, other in ((pr.left, pr.right), (pr.right, pr.left)):
                fact = self._affine_from_factor(col, idx, factor, other, b_col)
                if fact is not None:
                    return fact
        return None

    def _affine_from_factor(self, col: str, idx: int, factor: LinForm,
                            other: LinForm, b_col: Bound) -> AffineDef | None:
        a = factor.coeff(col)
        if a == 0:
            return None
        others = [(c, v) for c, v in factor.items() if c != col]
        if any(v % a for _, v in others) or factor.const % a:
            return None
        weights = {c: -(v // a) for c, v in others}
        offset = -(factor.const // a)
        prem: list[Fact] = [b_col]
        # window of k = col − Σ w·o − offset
        lo = -offset
        hi = (b_col.hi - 1) - offset
        for o, w in weights.items():
            b = self.bounds.get(o)
            if b is None or b.hi is None or b.lo < 0:
                return None
            prem.append(b)
            lo -= max(0, w) * (b.hi - 1)
            hi -= min(0, w) * (b.hi - 1)
        if not (lo > -P and hi < P):               # admitted-root sets below need this
            return None
        # admitted roots of the product within the window:
        #   chosen factor ≡ 0 ⟹ k = 0 (window excludes ±p);
        #   other factor ≡ 0  ⟺ a·k ≡ factor.const − other.const (mod p).
        # An exact affine definition needs the other factor's roots refuted;
        # if a root survives, the gadget only determines col MODULO the root
        # spacing (the carry case: roots {0, −2^16} ⟹ col known mod 2^16).
        k_h = pow(a % P, -1, P) * (factor.const - other.const) % P
        roots = [cand for cand in (k_h, k_h - P) if lo <= cand <= hi and cand != 0]
        if not roots:
            modulus = None
        else:
            modulus = 0
            for r in roots:
                modulus = math.gcd(modulus, abs(r))
            if modulus <= 1:
                return None                        # roots too dense — no usable claim
        return AffineDef(col, tuple(sorted(weights.items())), offset, modulus,
                         sources=(Src("constraint", idx),), premises=tuple(prem))
