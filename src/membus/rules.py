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
  Bounds then propagate to fixpoint across two-column ±1 constraints
  (``pos = neg + d``) when the shifted interval stays inside ``[0, p)`` —
  the forwarding equalities the `memory` pass emits keep the removed
  register read's byte bounds alive until the solver substitutes them.
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
from dataclasses import replace
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
from .linform import LinForm, bits_of, domain_gadget, linform, names, product
from . import propagate

P = BABYBEAR_PRIME

# Residue-enumeration cap for the range-check R2 form: 2^bits SMT-free loop
# iterations per candidate row. Corpus widths are ≤ 12 bits.
_MAX_ENUM_BITS = 16


def _proportional(a: tuple[tuple[str, int], ...],
                  b: tuple[tuple[str, int], ...]) -> int | None:
    """The scalar ``k`` with ``a == k·b`` over the field (same column set, one
    common ratio), or ``None`` if the coefficient vectors are not proportional.
    Used to recognise a constraint whose column part is a multiple of a range
    check's multiplicity, so the constraint pins the multiplicity's value."""
    da, db = dict(a), dict(b)
    if not db or da.keys() != db.keys():
        return None
    k: int | None = None
    for col, bc in db.items():
        try:
            kk = (da[col] * pow(bc % P, -1, P)) % P
        except ValueError:
            return None
        if k is None:
            k = kk
        elif k != kk:
            return None
    return k


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
        self._propagation = propagate.propagate(self)
        envs = propagate.surviving_envs(self, self._propagation)
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
        self._kinds_cache = {row.ordinal: self._kind(row) for row in self.mem}
        # Preserve the ORIGINAL (pre-fold) multiplicity expressions. `_kind`
        # classified each row from its original mult, but simplify_mem_rows below
        # rewrites self.mem, folding a symbolic mult to a constant. An EffKind
        # certificate must obligate `sources+premises ⊢ original_mult ≡ v`; if it
        # rendered the folded constant instead, the claim would be a tautology
        # and the fold's premises inert (a mis-fold would still certify).
        self._orig_mult = {row.ordinal: row.mult for row in self.mem}
        self.mem, exprs = propagate.simplify_mem_rows(
            self.mem, self._propagation, envs, self._ts_aliases)
        self._propagation = replace(self._propagation, exprs=exprs)

    def mem_src(self, row: MemRow) -> Src:
        return Src("bus", self._mem_bus_ordinal[row.ordinal])

    @functools.cached_property
    def constraint_cols(self) -> set[str]:
        """All column names appearing in the machine's constraints — cached so
        the refutation/surviving-env passes don't each rescan the machine."""
        return propagate._all_constraint_cols(self.machine)

    @functools.cached_property
    def _const_pins(self) -> dict[str, int]:
        """Columns pinned to a constant residue by the fixpoint of single-column
        linear constraints (substitute known pins, repeat). Kinds-independent, no
        propagation, so usable at bound-seeding time. The fixpoint (not a single
        pass) catches multi-step zeros like ``g = h, h = 0 ⟹ g = 0`` — needed to
        tell whether a range-check row is disabled (``mult ≡ 0``)."""
        pins: dict[str, int] = {}
        changed = True
        while changed:
            changed = False
            for con in self.machine.get("constraints", []):
                lf = linform(con)
                if lf is None:
                    continue
                lf = lf.subst(pins)
                if len(lf.coeffs) == 1:
                    col, a = lf.coeffs[0]
                    if col in pins:
                        continue
                    try:
                        pins[col] = (-lf.const * pow(a % P, -1, P)) % P
                    except ValueError:
                        continue
                    changed = True
        return pins

    @functools.cached_property
    def _single_col_src(self) -> dict[str, tuple[int, int]]:
        """col → (residue value, constraint idx) for single-column linear
        constraints — the citable evidence that a column holds a constant."""
        out: dict[str, tuple[int, int]] = {}
        for idx, con in enumerate(self.machine.get("constraints", [])):
            lf = linform(con)
            if lf is not None and len(lf.coeffs) == 1:
                col, a = lf.coeffs[0]
                if col in out:
                    continue
                try:
                    out[col] = ((-lf.const * pow(a % P, -1, P)) % P, idx)
                except ValueError:
                    continue
        return out

    def _range_mult_evidence(
        self, mult: Any) -> tuple[tuple[Src, ...], frozenset[Assumption]] | None:
        """Evidence that a range-check row is SENT (``mult != 0``), so its range
        genuinely bounds the arg. ``add_source`` asserts the range only when
        ``mult != 0``, so a bound may be emitted only with a certificate proof
        the row is active. Returns ``(sources, assumptions)`` proving
        ``mult != 0`` — the constraint sources, plus ``ACTIVE_SELECTOR`` when the
        row is gated by the block activation selector (granted ``= 1``, exactly
        as the memory-row kinds are). ``None`` when the row is disabled
        (``mult ≡ 0``, incl. multi-step) or its activity cannot be proven."""
        if mult is None:
            return ((), frozenset())       # no multiplicity: always sent
        lf = linform(mult)
        if lf is None:
            return None                    # non-linear mult: cannot analyse
        folded = lf.subst(self._const_pins)
        if not folded.coeffs and folded.const % P == 0:
            return None                    # disabled (mult ≡ 0), incl. multi-step
        # Cite the single-column pins that make the mult's columns constant, and
        # substitute them; the gate then rests on the residual.
        srcs: list[Src] = []
        subs: dict[str, int] = {}
        for col, _ in lf.coeffs:
            if col in self._single_col_src:
                v, idx = self._single_col_src[col]
                subs[col] = v
                srcs.append(Src("constraint", idx))
        resid = lf.subst(subs)
        if not resid.coeffs:               # residual is a constant
            return (tuple(srcs), frozenset()) if resid.const % P != 0 else None
        # Block-activation selector: a residual k·is_valid is nonzero because
        # ACTIVE_SELECTOR grants is_valid = 1 (the same assumption the memory
        # kinds rest on). Without it these is_valid-gated rows would drop.
        sel = self.active_selector
        if (self.assume_is_valid and sel is not None and resid.const == 0
                and len(resid.coeffs) == 1 and resid.coeffs[0][0] == sel):
            return (tuple(srcs), frozenset({Assumption.ACTIVE_SELECTOR}))
        # Symbolic residual: a constraint pinning it to a NONZERO constant (e.g.
        # sum(opcode flags) = 1) proves the row is sent.
        for idx, con in enumerate(self.machine.get("constraints", [])):
            lc = linform(con)
            if lc is None:
                continue
            lc = lc.subst(subs)
            k = _proportional(lc.coeffs, resid.coeffs)
            if k is None:
                continue
            # lc ≡ 0 is k·(resid − resid.const) + lc.const ≡ 0 ⟹ resid = resid.const − lc.const/k
            if (resid.const - lc.const * pow(k, -1, P)) % P != 0:
                return ((*srcs, Src("constraint", idx)), frozenset())
        return None

    @functools.cached_property
    def flags_by_access(self) -> dict[int, tuple[str, ...]]:
        """Opcode flag columns grouped by access, from the constraint columns."""
        return propagate._flags_by_access(self.constraint_cols)

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
        return self._kinds_cache

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
        v, prem = propagate.eval_mult_basis(lf, self._propagation)
        if v is not None:
            kind = {1: "send", P - 1: "recv", 0: "disabled"}.get(v)
            if kind is not None:
                return EffKind(row.ordinal, kind, sources=src, premises=prem)
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

    def _compute_bounds(self, *, include_kinds: bool) -> dict[str, Bound]:
        """Column → tightest known Bound fact — the single bound oracle.

        Seeds split into kinds-INDEPENDENT facts (range-check bus rows, a
        single-column residue pin, boolean/domain gadgets) and kinds-DEPENDENT
        ones (recv-data bytes under MEMBUS_BYTE, positional timestamps under
        TS_BOUND) that need the send/recv classification. ``propagate`` runs
        during ``Analysis`` construction, before ``kinds`` exists, so it uses
        ``_static_bounds`` (``include_kinds=False``); ``bounds``
        (``include_kinds=True``) layers the classified facts on top. Both go
        through this one computation, so the bounds ``propagate`` trusts as
        window premises are exactly a subset of the ``bounds`` that
        ``certify.all_facts`` proves — the two sets can never diverge.
        """
        out: dict[str, Bound] = {}

        def put(fact: Bound) -> None:
            cur = out.get(fact.col)
            if cur is None:
                out[fact.col] = fact
            elif fact.hi is not None and (cur.hi is None or fact.hi < cur.hi):
                out[fact.col] = fact

        for idx, bid, args, mult in range_bus_rows(self.machine):
            ev = self._range_mult_evidence(mult)
            if ev is None:
                continue        # disabled or unprovably-active row bounds nothing
            ev_src, asm = ev                     # evidence the row is sent
            src = (Src("bus", idx), *ev_src)
            if bid == VAR_RANGE and len(args) >= 2:
                bits = bits_of(args[1])
                if bits is None:
                    continue
                lf = linform(args[0])            # canonical: shape-independent
                if lf is None or lf.const != 0 or len(lf.coeffs) != 1:
                    continue
                col, c = lf.coeffs[0]
                if c == 1:
                    put(Bound(col, 0, 1 << bits, sources=src, assumptions=asm))
                    continue
                try:
                    s = pow(c % P, -1, P)
                except ValueError:
                    continue
                if s * (1 << bits) < P:          # no wrap ⟹ sound scaled bound
                    put(Bound(col, 0, s * (1 << bits), sources=src, assumptions=asm))
            elif bid == BITWISE:
                for a in args[:2]:
                    if isinstance(a, str):
                        put(Bound(a, 0, 1 << 8, sources=src, assumptions=asm))
            elif bid == TUPLE_RANGE:
                for a in args:
                    if isinstance(a, str):
                        put(Bound(a, 0, None, sources=src, assumptions=asm))

        if include_kinds:
            for row in self.mem:                 # membus-byte: recv data only
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

        for idx, con in enumerate(self.machine.get("constraints", [])):
            src = (Src("constraint", idx),)
            # A single-column linear constraint pins the column's residue
            # outright: a·col + c ≡ 0 (mod p) ⟹ col = (−c·a⁻¹) mod p — the claim
            # is exactly the canonical residue, no window argument needed.
            lf = linform(con)
            if lf is not None and len(lf.coeffs) == 1:
                col, a = lf.coeffs[0]
                try:
                    v = (-lf.const * pow(a % P, -1, P)) % P
                    put(Bound(col, v, v + 1, sources=src))
                except ValueError:
                    pass
                continue
            # Boolean / domain gadgets bound a column directly (no window).
            dg = domain_gadget(con)
            if dg is not None:
                put(Bound(dg[0], 0, dg[1], sources=src))
                continue
            pr = product(con)
            if pr is not None and (
                    pr.left.coeffs == pr.right.coeffs
                    and pr.right.const == pr.left.const - 1
                    and len(pr.left.coeffs) == 1
                    and pr.left.coeffs[0][1] == 1
                    # (col+a)(col+a-1)=0 has roots {−a, 1−a}: [0,2) only for a=0.
                    and pr.left.const == 0):
                put(Bound(pr.left.coeffs[0][0], 0, 2, sources=src))

        # Closure: propagate bounds across two-column ±1 constraints
        # (``pos − neg + const = 0``, i.e. ``pos = neg + d`` with
        # ``d = −const``). Sound as an integer statement when the shifted
        # interval stays inside one residue period: ``lo+d ≥ 0`` and
        # ``hi+d ≤ p``. This keeps key recovery stable across the window the
        # `memory` pass opens: it removes the register read whose recv data
        # carried the base bytes' MEMBUS_BYTE bounds, but adds forwarding
        # equalities (``read.data == written.data``) that the bound survives
        # through until the solver substitutes the dead columns away.
        changed = True
        while changed:
            changed = False
            for idx, pos, neg, const in self._two_col_gaps:
                for src_col, dst_col, d in ((neg, pos, -const), (pos, neg, const)):
                    b = out.get(src_col)
                    if b is None or b.hi is None:
                        continue
                    lo, hi = b.lo + d, b.hi + d
                    if lo < 0 or hi > P:
                        continue                 # would leave [0, p): wrap branch
                    cur = out.get(dst_col)
                    if cur is None or cur.hi is None or hi < cur.hi:
                        out[dst_col] = Bound(dst_col, lo, hi,
                                             sources=(Src("constraint", idx),),
                                             premises=(b,))
                        changed = True
        return out

    @functools.cached_property
    def _static_bounds(self) -> dict[str, Bound]:
        """Kinds-independent bounds — available during ``Analysis``
        construction, so ``propagate`` can use them as window premises before
        ``kinds`` (which depends on propagation) exists."""
        return self._compute_bounds(include_kinds=False)

    @functools.cached_property
    def bounds(self) -> dict[str, Bound]:
        """Column → tightest known Bound fact (all seeds, incl. kinds-gated)."""
        return self._compute_bounds(include_kinds=True)

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

    def _ungate_lessthan(self, con: Any) -> tuple[Any, tuple[Fact, ...]]:
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
        prop = self._propagation
        # Collect the facts that justify the fold/peel, so _recv_upper_constraints
        # can premise the RecvUpper with them. The certificate re-expands the RAW
        # gated source, so without the selector's LinZero/pins z3 satisfies the
        # `selector = 0` disjunct and the bound spuriously fails (sat). Folded
        # pins are premised for the same reason (the raw source keeps the column).
        prem: list[Fact] = [prop.pins[c] for c in names(con) if c in prop.pins]
        expr = propagate._fold_pins(con, prop, self._ts_aliases)
        while isinstance(expr, list) and len(expr) == 3 and expr[1] == "*":
            va, pa = propagate.eval_mult_basis(linform(expr[0]), prop)
            vb, pb = propagate.eval_mult_basis(linform(expr[2]), prop)
            if va == 0 or vb == 0:
                return None, ()
            if va == 1:
                prem.extend(pa)
                expr = expr[2]
            elif vb == 1:
                prem.extend(pb)
                expr = expr[0]
            else:
                break
        return expr, tuple(prem)

    def _recv_upper_constraints(self) -> list[RecvUpper]:
        # A RecvUpper needs exactly one recv-witness column; skip the (majority
        # of) constraints touching none before the costly fold / ungate.
        witnesses = self.ts_domain[1]
        out = []
        for idx, con in enumerate(self.machine.get("constraints", [])):
            if witnesses.isdisjoint(names(con)):
                continue
            body, ungate_prem = self._ungate_lessthan(con)
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
                sources=(Src("constraint", idx),), premises=prem + ungate_prem))
        return out

    def _recv_upper_range_checks(self) -> list[RecvUpper]:
        out = []
        for idx, bid, args, mult in range_bus_rows(self.machine):
            if bid != VAR_RANGE or len(args) < 2:
                continue
            ev = self._range_mult_evidence(mult)
            if ev is None:
                continue        # disabled or unprovably-active row constrains nothing
            ev_src, asm = ev
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
                sources=(Src("bus", idx), *ev_src), premises=prem, assumptions=asm))
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
