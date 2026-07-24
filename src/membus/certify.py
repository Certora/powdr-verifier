"""SMT certificates: one query per fact, UNSAT ⟺ the extraction is justified.

Every fact type knows its proof obligation; this module renders it as an
SMT-LIB query:

- every column is an Int constrained to the field-residue domain ``[0, p)``;
- each **source** is asserted with its native semantics — a constraint as
  ``E ≡ 0 (mod p)`` (a product constraint as the prime-field disjunction
  ``G ≡ 0 ∨ H ≡ 0``), a range-check bus row as ``E mod p ∈ [0, 2^bits)``;
- each **premise fact** is asserted as its integer claim (its own certificate
  justifies it — certificates compose along the fact DAG);
- each named **assumption** is asserted explicitly where it attaches:
  TS_BOUND and MEMBUS_BYTE *grant* the slot-derived Bound facts (those
  certificates are visibly trivial — the fact rests on the assumption);
  ACTIVE_SELECTOR asserts ``selector = 1`` for the structurally recognized
  gating column. Nothing is asserted by column name;
- the fact's claim is asserted **negated**.

``(check-sat)`` must return ``unsat``. A ``sat`` result means the rule
accepted something its premises do not justify — the failure mode this whole
design exists to catch — and the model is a concrete counterexample witness.
"""
from __future__ import annotations

import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from src.lens.normalize import BABYBEAR_PRIME

from .facts import (
    AffineDef, Assumption, Bound, EffKind, ExprEval, Fact, Gap, LinZero, Pin, RecvUpper, TS_MAX,
)
from .busmodel import BITWISE, VAR_RANGE
from .linform import flatten_product, linform, names
from .rules import Analysis

P = BABYBEAR_PRIME

_Z3_CANDIDATES = ("z3",)


def _smt_sym(col: str) -> str:
    return f"|{col}|"


def _expr(e: Any) -> str:
    """Render a dump expression as SMT-LIB (Ints; columns as |quoted| consts)."""
    if isinstance(e, bool):
        raise ValueError(f"unexpected bool expr: {e!r}")
    if isinstance(e, int):
        return str(e) if e >= 0 else f"(- {-e})"
    if isinstance(e, str):
        return _smt_sym(e)
    if isinstance(e, list) and len(e) == 2 and e[0] == "-":
        return f"(- {_expr(e[1])})"
    if isinstance(e, list) and len(e) == 3:
        lhs, op, rhs = e
        if op not in ("+", "-", "*"):
            raise ValueError(f"unsupported op {op!r} in {e!r}")
        return f"({op} {_expr(lhs)} {_expr(rhs)})"
    raise ValueError(f"cannot render expr: {e!r}")


def _lin(coeffs: dict[str, int] | list[tuple[str, int]], const: int) -> str:
    parts = [f"(* {c} {_smt_sym(col)})" if c >= 0 else f"(* (- {-c}) {_smt_sym(col)})"
             for col, c in (coeffs.items() if isinstance(coeffs, dict) else coeffs)]
    parts.append(str(const) if const >= 0 else f"(- {-const})")
    return parts[0] if len(parts) == 1 else "(+ " + " ".join(parts) + ")"


@dataclass
class Certificate:
    fact: Fact
    smt2: str
    label: str


class _Query:
    def __init__(self, an: Analysis, title: str):
        self.an = an
        self.lines: list[str] = [f"; {title}", f"; field prime p = {P}"]
        self.cols: set[str] = set()
        self.asserted_sources: set = set()
        self.asserted_facts: set[int] = set()
        self._quot = 0

    def comment(self, s: str) -> None:
        self.lines.append(f"; {s}")

    def declare(self, e: Any) -> None:
        self.cols |= {c for c in names(e) if isinstance(c, str)}

    def assert_(self, s: str) -> None:
        self.lines.append(f"(assert {s})")

    def quotient(self) -> str:
        """Fresh field-reduction quotient variable (explicit-quotient encoding:
        ``E ≡ r (mod p)`` becomes ``E = q·p + r`` — pure LIA, no `mod` terms
        with field-sized coefficients, which time z3 out)."""
        self._quot += 1
        q = f"q{self._quot}"
        self.lines.append(f"(declare-const {q} Int)")
        return q

    def _canon_expr(self, e: Any) -> str:
        """SMT rendering of ``e``, in canonical signed coefficients when ``e``
        is linear. ``E_canon ≡ E_raw (mod p)`` holds coefficient-wise by
        construction of LinForm (each raw coefficient minus its canonical
        representative is a multiple of p) — small coefficients keep the
        quotient's range tiny, which is what makes these queries fast."""
        lf = linform(e)
        if lf is None:
            return _expr(e)
        self.declare(e)
        return _lin(list(lf.coeffs), lf.const)

    def field_zero(self, e: Any) -> str:
        """``E ≡ 0 (mod p)`` via an explicit quotient, canonical coefficients."""
        return f"(= {self._canon_expr(e)} (* {P} {self.quotient()}))"

    # -- source material ------------------------------------------------------

    def add_source(self, src) -> None:
        if src in self.asserted_sources:
            return
        self.asserted_sources.add(src)
        if src.kind == "constraint":
            con = self.an.machine["constraints"][src.index]
            self.declare(con)
            if isinstance(con, list) and len(con) == 3 and con[1] == "*":
                # prime field: F1·…·Fn ≡ 0 ⟹ ⋁ Fi ≡ 0 (p is prime). Split ALL
                # factors, not just the outermost two: a domain gadget
                # f·(f-1)·(f-2) must yield three LINEAR disjuncts, else the
                # nested `(f-1)·(f-2)` disjunct stays quadratic and z3 times out
                # (the [0,n) domain bound then spuriously fails to certify).
                factors = flatten_product(con)
                self.comment(f"source constraint[{src.index}] "
                             f"(product; prime-field split, {len(factors)} factors)")
                self.assert_("(or " + " ".join(self.field_zero(f) for f in factors) + ")")
            else:
                self.comment(f"source constraint[{src.index}]")
                self.assert_(self.field_zero(con))
        else:  # bus row
            b = self.an.machine["bus_interactions"][src.index]
            bid, args = b.get("id"), b.get("args", [])
            if bid == VAR_RANGE and len(args) >= 2 and isinstance(args[1], int):
                self.declare(args[0])
                self.comment(f"source bus[{src.index}]: VariableRangeChecker "
                             f"(value residue in [0, 2^{args[1]}))")
                q, r = self.quotient(), self.quotient()
                self.assert_(f"(= {self._canon_expr(args[0])} (+ (* {P} {q}) {r}))")
                self.assert_(f"(and (<= 0 {r}) (< {r} {1 << args[1]}))")
                self._scaled_hint(args[0], q, r)
            elif bid == BITWISE:
                for a in args[:2]:
                    if isinstance(a, str):
                        self.declare(a)
                        self.comment(f"source bus[{src.index}]: BitwiseLookup operand is a byte")
                        self.assert_(f"(< {_smt_sym(a)} 256)")
            else:
                self.comment(f"source bus[{src.index}] (id {bid}): no direct SMT semantics; "
                             f"granted by a named assumption below")

    def _scaled_hint(self, arg: Any, q: str, r: str) -> None:
        """Entailed hint lemma for a *scaled* range-check arg ``c·col``.

        From ``c·col = q·p + r`` and the emission-verified constant identity
        ``s·c = 1 + k·p`` (``s = c⁻¹ mod p``), multiplying the source by ``s``
        gives ``col = s·r + p·(s·q − k·col)``. Asserting it with ``t`` *defined*
        as that expression adds only an entailed consequence (sound for UNSAT
        checking), and hands z3 the modular-inverse step it cannot find itself.
        """
        lf = linform(arg)
        if lf is None or len(lf.coeffs) != 1 or lf.const != 0:
            return
        col, c = lf.coeffs[0]
        if c in (1, -1):
            return
        try:
            s = pow(c % P, -1, P)
        except ValueError:
            return
        k, rem = divmod(s * c - 1, P)
        assert rem == 0, "inverse identity must be exact"
        self._quot += 1
        t = f"t{self._quot}"
        self.comment(f"hint (entailed): s = c^-1 = {s}, s*{c} = 1 + {k}*p; "
                     f"source * s ==> col = s*r + p*t")
        self.lines.append(
            f"(define-fun {t} () Int (- (* {s} {q}) (* {k} {_smt_sym(col)})))")
        self.assert_(f"(= {_smt_sym(col)} (+ (* {s} {r}) (* {P} {t})))")

    # -- premise facts / assumptions ------------------------------------------

    def add_premise(self, f: Fact) -> None:
        if id(f) in self.asserted_facts:
            return
        self.asserted_facts.add(id(f))
        self.comment(f"premise fact: {f}")
        self.assert_(self.claim(f))
        for a in f.assumptions:
            self.add_assumption_for(f, a)

    # The exact [lo, hi) domain each assumption licenses. A Bound tagged with
    # the assumption is granted only at this value — a byte is [0, 256), a
    # timestamp slot is [0, 2^29). Anything else is not what the assumption
    # means and must not be granted.
    _GRANTED_BOUND = {
        Assumption.MEMBUS_BYTE: (0, 1 << 8),
        Assumption.TS_BOUND: (0, TS_MAX),
    }

    def add_assumption_for(self, f: Fact, a: Assumption) -> None:
        self.comment(f"named assumption: {a.name} -- {a.value}")
        # MEMBUS_BYTE and TS_BOUND *grant* their slot-derived Bound facts
        # outright: the granted claim is asserted so the certificate is
        # (visibly) trivial — the fact rests on the assumption. But grant ONLY
        # the assumption's exact domain; asserting the claim for any other
        # (lo, hi) would vacuously certify a wrong-valued or mis-identified
        # Bound. A mismatch is left ungranted so it surfaces as a failing (sat)
        # certificate. ACTIVE_SELECTOR fixes the recognized gating column to 1.
        grant = self._GRANTED_BOUND.get(a)
        if grant is not None and isinstance(f, Bound):
            if (f.lo, f.hi) == grant:
                self.assert_(self.claim(f))
            else:
                self.comment(f"NOT granted: {a.name} licenses only [{grant[0]}, "
                             f"{grant[1]}), but this Bound is [{f.lo}, {f.hi})")
        if a is Assumption.ACTIVE_SELECTOR and self.an.active_selector is not None:
            sel = self.an.active_selector
            self.declare(sel)
            self.assert_(f"(= {_smt_sym(sel)} 1)")

    def _assert_flag_refutation(self, pin: Pin) -> None:
        """Grant each deciding flag its PROVEN value domain — the certified
        ``_static_bounds`` Bound (a domain gadget ``f·(f-1)·…·(f-(n-1))=0`` gives
        ``[0,n)``), cited as a premise.

        Opcode flags are frequently TERNARY, so hard-coding ``flag ≤ 1`` was
        unsound: it deleted the ``f=2`` case, and an ``is_load`` value unique
        only over ``{0,1}`` (but not over the real domain) then certified. We do
        NOT grant ``is_load`` a domain — the deciding mux (a source) determines
        it from the flags. A flag with no proven finite domain gets no grant;
        the sources must then constrain it or the certificate fails (safe).

        The real obligation — that under those domains the deciding constraints
        (this pin's sources) admit no ``is_load`` value other than ``pin.value``
        — is discharged by z3 against the negated claim ``finish`` asserts. We
        must NOT assert a "witness" fixing ``is_load = pin.value`` (vacuous
        UNSAT for any value) nor the refuted value infeasible (asserts the
        conclusion). Both were earlier bugs.
        """
        if not pin.refute_flags:
            return
        for col in (*pin.refute_flags, pin.col):
            b = self.an._static_bounds.get(col)
            if b is None or b.lo != 0 or b.hi is None:
                continue   # no proven finite domain (e.g. is_load): the
                # deciding sources must constrain it, or the certificate fails
            self.declare(col)
            self.assert_(f"(and (<= 0 {_smt_sym(col)}) (< {_smt_sym(col)} {b.hi}))")
            self.add_premise(b)   # the domain is a certified fact, cite it

    def claim(self, f: Fact) -> str:
        if isinstance(f, Bound):
            self.declare(f.col)
            if f.hi is None:
                return f"(<= {f.lo} {_smt_sym(f.col)})"
            return f"(and (<= {f.lo} {_smt_sym(f.col)}) (< {_smt_sym(f.col)} {f.hi}))"
        if isinstance(f, Gap):
            self.declare(f.later)
            self.declare(f.earlier)
            return f"(= {_smt_sym(f.later)} (+ {_smt_sym(f.earlier)} {f.gap}))"
        if isinstance(f, RecvUpper):
            self.declare(f.pv)
            self.declare(f.fs)
            rhs = (f"(+ {_smt_sym(f.fs)} {f.const})" if f.const >= 0
                   else f"(- {_smt_sym(f.fs)} {-f.const})")
            return f"(<= {_smt_sym(f.pv)} {rhs})"
        if isinstance(f, AffineDef):
            self.declare(f.col)
            for o, _ in f.weights:
                self.declare(o)
            rhs = _lin(list(f.weights), f.offset)
            if f.modulus is None:
                return f"(= {_smt_sym(f.col)} {rhs})"
            return f"(= (mod (- {_smt_sym(f.col)} {rhs}) {f.modulus}) 0)"
        if isinstance(f, EffKind):
            # The ORIGINAL multiplicity, not the folded one in self.an.mem: for a
            # propagation-folded mult the folded value is a constant, so the
            # claim would be a tautology and the premises inert. Rendering the
            # original expr makes `premises ⊢ original_mult ≡ v` the real
            # obligation z3 must discharge.
            mult = self.an._orig_mult[f.ordinal]
            self.declare(mult)
            v = {"send": 1, "recv": P - 1, "disabled": 0}[f.kind]
            return f"(= (mod {_expr(mult)} {P}) {v})"
        if isinstance(f, Pin):
            self.declare(f.col)
            if f.refute_flags:
                self._assert_flag_refutation(f)
            return f"(= {_smt_sym(f.col)} {f.value})"
        if isinstance(f, LinZero):
            for col, _ in f.coeffs:
                self.declare(col)
            return f"(= {_lin(list(f.coeffs), f.const)} 0)"
        if isinstance(f, ExprEval):
            self.declare(f.expr)
            return f"(= {_expr(f.expr)} {f.value})"
        raise TypeError(f"no claim rendering for {type(f).__name__}")

    def finish(self, negated_claim: str) -> str:
        decls: list[str] = []
        for c in sorted(self.cols):
            decls.append(f"(declare-const {_smt_sym(c)} Int)")
            decls.append(f"(assert (and (<= 0 {_smt_sym(c)}) (< {_smt_sym(c)} {P})))")
        body = self.lines
        return "\n".join([
            "(set-logic ALL)",
            *decls,
            *body,
            "; negated claim -- must be UNSAT",
            f"(assert (not {negated_claim}))",
            "(check-sat)",
            "",
        ])


def certificate(an: Analysis, fact: Fact) -> Certificate:
    """Build the SMT certificate for one fact."""
    q = _Query(an, f"certificate for: {fact}")
    for src in fact.sources:
        q.add_source(src)
    for p in fact.premises:
        q.add_premise(p)
    for a in fact.assumptions:
        q.add_assumption_for(fact, a)
    claim = q.claim(fact)
    label = f"{type(fact).__name__}: {fact}"
    return Certificate(fact, q.finish(claim), label)


def all_facts(an: Analysis) -> list[Fact]:
    """Every fact the deduction layer can consume from this dump: kinds of the
    memory rows, column bounds, timestamp gaps, recv bounds, and the affine
    definitions of the pointer limbs."""
    out: list[Fact] = []
    prop = an._propagation
    out += list(prop.pins.values())
    out += list(prop.zeros)
    out += list(prop.exprs)
    out += [k for k in an.kinds.values() if k is not None]
    out += list(an.bounds.values())
    out += list(an.gaps)
    for fs in an.recv_uppers.values():
        out += fs
    from .linform import linform
    seen: set[str] = set()
    for row in an.mem:
        lf = linform(row.ptr)
        if lf is None:
            continue
        for col in lf.columns:
            if col not in seen:
                seen.add(col)
                d = an.affine(col)
                if d is not None:
                    out.append(d)
    return out


def find_z3() -> str | None:
    for c in _Z3_CANDIDATES:
        w = shutil.which(c)
        if w:
            return w
    return None


def run_z3(smt2: str, z3: str, timeout_s: int = 30) -> str:
    """Run one certificate; returns 'unsat' | 'sat' | 'unknown' | 'error:…'.

    Two phases. Phase 1 runs with ``tactic.default_tactic=smt`` under a short
    cap: z3's default tactic burns ~7-10 s in a pre-solver on the
    quotient-encoded queries before falling through to `smt`, which closes
    them instantly on recent z3 (see the z3-hard-certificate-queries note in
    the research notebook). On z3 4.16.0 the direct smt tactic instead TIMES
    OUT on those queries (fixed somewhere before 4.17-dev 316d249b), so a
    non-answer falls back to the default tactic with the full budget."""

    def once(args: list[str], cap: int) -> str:
        try:
            proc = subprocess.run([z3, "-in", f"-T:{cap}", *args], input=smt2,
                                  capture_output=True, text=True, timeout=cap + 5)
        except (OSError, subprocess.TimeoutExpired) as e:
            return f"error: {e}"
        res = (proc.stdout.strip().splitlines() or ["?"])[-1]
        return res if res in ("sat", "unsat", "unknown") else f"error: {res[:80]}"

    quick = once(["tactic.default_tactic=smt"], min(5, timeout_s))
    if quick in ("sat", "unsat"):
        return quick
    return once([], timeout_s)


def certify_dump(data: Any, mem_id: int = 1, assume_is_valid: bool = True,
                 run: bool = False, out_dir: Path | None = None,
                 z3_path: str | None = None) -> list[dict]:
    """Certificates for every fact of one dump; optionally write + run them.

    ``z3_path`` overrides the binary used for ``run`` (default: ``z3`` on
    PATH)."""
    an = Analysis(data, mem_id, assume_is_valid)
    z3 = None
    if run:
        if z3_path is not None:
            if not (Path(z3_path).is_file() or shutil.which(z3_path)):
                raise ValueError(f"certify: z3 binary not found: {z3_path}")
            z3 = z3_path
        else:
            z3 = find_z3()
            if z3 is None:
                raise ValueError(
                    "certify: --run requested but no z3 binary found on PATH "
                    "(use --z3-path)")
    results: list[dict] = []
    for i, fact in enumerate(all_facts(an)):
        cert = certificate(an, fact)
        rec: dict[str, Any] = {
            "index": i,
            "type": type(fact).__name__,
            "fact": str(fact),
            "sources": [str(s) for s in fact.sources],
            "assumptions": sorted(a.name for a in fact.all_assumptions()),
        }
        if out_dir is not None:
            f = out_dir / f"cert_{i:04d}_{type(fact).__name__}.smt2"
            f.write_text(cert.smt2)
            rec["file"] = str(f)
        if run:
            rec["result"] = run_z3(cert.smt2, z3)
        results.append(rec)
    return results
