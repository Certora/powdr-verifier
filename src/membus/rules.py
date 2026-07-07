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
- **Timestamp domain (positional).** A column is a **clock** because it is
  the single column in the timestamp slot (``args[6]``) of a send, a **recv
  witness** because it sits in a recv's slot — never because of its name.
  Slot columns get ``Bound(col, 0, 2^29)`` by ``TS_BOUND``; columns *linked*
  to a clock by a two-column ±1 constraint (the clocks of instructions with
  no memory access) join the clock domain with a **derived** bound
  (linked bound + |gap|), premised on the constraint — no fresh assumption.
- **R1 → Gap.** A constraint ``a − b + c = 0`` over two clock-domain columns
  reads as the integer gap ``a = b − c``, premised on both columns' bounds
  (window < p).
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
  under ``--assume-is-valid`` — ``±g`` where ``g`` is the **structurally
  recognized activation selector**: the one column that gates every
  non-constant memory multiplicity in the dump (``ACTIVE_SELECTOR``). Two
  different gating columns ⟹ no selector, those rows stay unresolved.
"""
from __future__ import annotations

import functools
import math
from typing import Any

from src.lens.loader import machine_of
from src.lens.normalize import BABYBEAR_PRIME

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
from .linform import LinForm, bits_of, linform, names, product
from . import propagate

P = BABYBEAR_PRIME

# Residue-enumeration cap for the range-check R2 form: 2^bits SMT-free loop
# iterations per candidate row. Corpus widths are ≤ 12 bits.
_MAX_ENUM_BITS = 16


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
        pins, zeros, decoding = propagate.propagate(self)
        self._propagation = (pins, zeros)
        envs = propagate.surviving_envs(self, pins, decoding)
        substitutions = data.get("substitutions") if isinstance(data, dict) else None
        send_cols: set[str] = set()
        for row in self.mem:
            k = self._kind(row)
            if k is not None and k.kind == "send":
                col = self._slot_col(row.ts)
                if col is not None:
                    send_cols.add(col)
        self._ts_aliases = propagate.send_ts_aliases(
            send_cols, self._two_col_gaps, substitutions)
        self.mem = [
            propagate.simplify_mem_row(r, pins, zeros, envs, self._ts_aliases)
            for r in self.mem
        ]

    def mem_src(self, row: MemRow) -> Src:
        return Src("bus", self._mem_bus_ordinal[row.ordinal])

    # -- Kind + activation selector (structural) ------------------------------

    @functools.cached_property
    def active_selector(self) -> str | None:
        """The one column gating **every active** memory multiplicity
        (``mult = ±g``, coefficient ±1, no constant part) — the final APC's
        activation selector, recognized by structure.

        Block activation means ALL of the block's interactions are gated: a
        dump that mixes constant ±1 multiplicities with gated ones has no
        block selector (the gate would be a per-instruction variant flag,
        which ``--assume-is-valid`` does not license). None also when two
        different gating columns appear, or a symbolic mult isn't ``±g``.
        """
        sel: str | None = None
        has_const_active = False
        for row in self.mem:
            lf = linform(row.mult)
            if lf is None:
                continue                        # flag-mux products stay unresolved
            if lf.is_const:
                if lf.const % P != 0:
                    has_const_active = True     # a ±1 row not behind any gate
                continue
            if len(lf.coeffs) != 1 or lf.const != 0 or lf.coeffs[0][1] not in (1, -1):
                return None                     # a non-±g symbolic mult ⟹ no selector
            g = lf.coeffs[0][0]
            if sel is None:
                sel = g
            elif sel != g:
                return None                     # two gating columns ⟹ ambiguous
        return None if has_const_active else sel

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
        if (self.assume_is_valid and self.active_selector is not None
                and lf.coeffs == ((self.active_selector, lf.coeffs[0][1]),)):
            kind = "send" if lf.coeffs[0][1] == 1 else "recv"   # g := 1
            return EffKind(row.ordinal, kind, sources=src,
                           assumptions=frozenset({Assumption.ACTIVE_SELECTOR}))
        pins, zeros = self._propagation
        v = propagate.eval_mult(lf, pins, zeros)
        if v is not None:
            kind = {1: "send", P - 1: "recv", 0: "disabled"}.get(v)
            if kind is not None:
                return EffKind(row.ordinal, kind, sources=src)
        return None

    # -- Timestamp domain (positional) ----------------------------------------

    @staticmethod
    def _slot(ts_arg) -> tuple[str, int] | None:
        """A timestamp-slot arg parsed as ``(col, offset)`` — the arg is
        ``col + offset`` with coefficient 1 — or None."""
        lf = linform(ts_arg)
        if lf is not None and len(lf.coeffs) == 1 and lf.coeffs[0][1] == 1:
            return lf.coeffs[0][0], lf.const
        return None

    @classmethod
    def _slot_col(cls, ts_arg) -> str | None:
        s = cls._slot(ts_arg)
        return s[0] if s is not None else None

    @functools.cached_property
    def _two_col_gaps(self) -> list[tuple[int, str, str, int]]:
        """Two-column ±1 linear constraints as ``(idx, pos, neg, const)`` —
        i.e. ``pos − neg + const = 0``. Shared by the domain closure and R1."""
        out = []
        for idx, con in enumerate(self.machine.get("constraints", [])):
            lf = linform(con)
            if lf is None or len(lf.coeffs) != 2:
                continue
            (a, ca), (b, cb) = lf.coeffs
            if {ca, cb} != {1, -1}:
                continue
            pos, neg = (a, b) if ca == 1 else (b, a)
            out.append((idx, pos, neg, lf.const))
        return out

    @functools.cached_property
    def ts_domain(self) -> tuple[set[str], set[str], dict[str, Bound]]:
        """``(clock_cols, witness_cols, ts_bounds)``, all positional.

        Seed: the slot column of every resolved send is a clock, of every
        resolved recv a witness — each gets ``Bound(col, 0, 2^29)`` granted by
        ``TS_BOUND`` (a statement about columns occurring in the SLOT, so it
        covers post-`inlining` dumps where every occurrence is ``base + off``
        with a positive offset).

        Closure: a two-column ±1 constraint extends the clock domain — the
        clocks of instructions that touch no memory, needed to chain the send
        order (in particular the chain base, which cross-circuit alignment
        relies on). Forward links (``new = known + d``, ``d ≥ 0``) get a
        **derived** bound (``[0, hi_known + d)`` is residue-unique); backward
        links admit the ``+p`` wrap branch, so their bound is **granted by
        TS_BOUND** (the linked column is a clock of the same block) rather
        than derived.

        A column claimed as both clock and witness is dropped from both
        (ambiguous ⟹ no facts about it).
        """
        clocks: set[str] = set()
        witnesses: set[str] = set()
        bounds: dict[str, Bound] = {}
        for row in self.mem:
            k = self.kinds.get(row.ordinal)
            if k is None or k.kind == "disabled":
                continue
            col = self._slot_col(row.ts)
            if col is None:
                continue
            (clocks if k.kind == "send" else witnesses).add(col)
            if col not in bounds:
                bounds[col] = Bound(col, 0, TS_MAX, sources=(self.mem_src(row),),
                                    premises=(k,) if k.assumptions else (),
                                    assumptions=frozenset({Assumption.TS_BOUND}))
        both = clocks & witnesses
        clocks -= both
        witnesses -= both
        for col in both:
            bounds.pop(col, None)

        # closure: forward links derive a bound, backward links get TS_BOUND
        changed = True
        while changed:
            changed = False
            for idx, pos, neg, const in self._two_col_gaps:
                # pos - neg + const = 0  =>  pos = neg - const ; neg = pos + const
                for known, new, d in ((neg, pos, -const), (pos, neg, const)):
                    if known not in bounds or known not in clocks:
                        continue
                    if new in witnesses:
                        continue
                    if d >= 0:
                        kb = bounds[known]
                        hi = kb.hi + d
                        if hi >= P:
                            continue
                        if new not in bounds or bounds[new].hi > hi:
                            bounds[new] = Bound(new, 0, hi,
                                                sources=(Src("constraint", idx),),
                                                premises=(kb,))
                            clocks.add(new)
                            changed = True
                    elif new not in clocks:
                        bounds.setdefault(new, Bound(
                            new, 0, TS_MAX, sources=(Src("constraint", idx),),
                            assumptions=frozenset({Assumption.TS_BOUND})))
                        clocks.add(new)
                        changed = True
        return clocks, witnesses, bounds

    @property
    def clock_cols(self) -> set[str]:
        return self.ts_domain[0]

    @property
    def witness_cols(self) -> set[str]:
        return self.ts_domain[1]

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
                bits = bits_of(args[1])
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
        for fact in self.ts_domain[2].values():  # positional timestamp bounds
            put(fact)
        return out

    def _window(self, terms: list[tuple[str, int]], const: int,
                ) -> tuple[int, int, tuple[Fact, ...]] | None:
        """Integer window ``[lo, hi]`` of ``Σ coeff·col + const``; every
        column needs a Bound fact with a known width (timestamp columns get
        theirs from the positional TS_BOUND facts like everything else).
        None if some column is unbounded."""
        lo = hi = const
        prem: list[Fact] = []
        for col, c in terms:
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
        clocks = self.clock_cols
        out = []
        for idx, pos, neg, const in self._two_col_gaps:
            if pos not in clocks or neg not in clocks:
                continue
            bp, bn = self.bounds.get(pos), self.bounds.get(neg)
            if bp is None or bp.hi is None or bn is None or bn.hi is None:
                continue
            # window: pos − neg + const ∈ (const − hi_neg, const + hi_pos) ⊂ (−p, p)
            if not (const - bn.hi > -P and const + bp.hi < P):
                continue
            gap = -const                           # pos = neg + gap
            if gap == 0 or abs(gap) >= TS_MAX:     # usability guard
                continue
            later, earlier = (pos, neg) if gap > 0 else (neg, pos)
            out.append(Gap(later, earlier, abs(gap), sources=(Src("constraint", idx),),
                           premises=(bp, bn)))
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
        clocks, witnesses, _ = self.ts_domain
        fs = [(c, v) for c, v in lf.items() if c in clocks]
        pv = [(c, v) for c, v in lf.items() if c in witnesses]
        rest = [(c, v) for c, v in lf.items() if c not in clocks and c not in witnesses]
        return fs, pv, rest

    def _ungate_lessthan(self, con: Any) -> Any:
        """Fold pins / timestamp aliases into a constraint and peel selector
        factors off a gated LessThan.

        A LessThan may appear as ``sel · (fs − pv − …) = 0`` where ``sel`` is a
        pinned column (``is_valid``) or a linear selector propagation proves
        equals 1 (``Σ opcode_flags``, whose ``Σ − 1`` is a known zero). It may
        also reference a per-access ``from_state`` clock that timestamp
        normalization folded onto the shared base. Fold both, then drop any
        top-level product factor that evaluates to 1; a factor of 0 makes the
        constraint vacuous (no bound), signalled by ``None``.
        """
        pins, zeros = self._propagation
        expr = propagate._fold_pins(con, pins, self._ts_aliases)
        while isinstance(expr, list) and len(expr) == 3 and expr[1] == "*":
            va = propagate.eval_expr(pins, zeros, expr[0])
            vb = propagate.eval_expr(pins, zeros, expr[2])
            if va == 0 or vb == 0:
                return None
            if va == 1:
                expr = expr[2]
            elif vb == 1:
                expr = expr[0]
            else:
                break
        return expr

    def _recv_upper_constraints(self) -> list[RecvUpper]:
        # A RecvUpper needs exactly one recv-witness column; skip the (majority
        # of) constraints touching none before the costly fold / ungate.
        witnesses = self.ts_domain[1]
        out = []
        for idx, con in enumerate(self.machine.get("constraints", [])):
            if witnesses.isdisjoint(names(con)):
                continue
            body = self._ungate_lessthan(con)
            if body is None:
                continue
            lf = linform(body)
            if lf is None:
                continue
            fs, pv, rest = self._split_ts(lf)
            if len(fs) != 1 or len(pv) != 1 or fs[0][1] != 1 or pv[0][1] != -1:
                continue
            if any(v >= 0 for _, v in rest):
                continue
            win = self._window(list(lf.coeffs), lf.const)
            if win is None:
                continue
            lo, hi, prem = win
            if not (lo > -P and hi < P):           # k ≡ 0 (mod p) ⟹ k = 0
                continue
            out.append(RecvUpper(
                pv[0][0], fs[0][0], lf.const,
                sources=(Src("constraint", idx),), premises=prem))
        return out

    def _recv_upper_range_checks(self) -> list[RecvUpper]:
        out = []
        for idx, bid, args in range_bus_rows(self.machine):
            if bid != VAR_RANGE or len(args) < 2:
                continue
            bits = bits_of(args[1])
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
            win = self._window([(fs[0][0], 1), (pv[0][0], -1), *nrest], nconst)
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
                sources=(Src("bus", idx),), premises=prem))
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
