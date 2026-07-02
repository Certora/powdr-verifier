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

from .facts import AffineDef, Assumption, Bound, EffKind, Fact, Gap, RecvUpper
from .linform import linform, names
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
                # prime field: G·H ≡ 0 ⟹ G ≡ 0 ∨ H ≡ 0 (p is prime)
                self.comment(f"source constraint[{src.index}] (product; prime-field split)")
                self.assert_(f"(or {self.field_zero(con[0])} {self.field_zero(con[2])})")
            else:
                self.comment(f"source constraint[{src.index}]")
                self.assert_(self.field_zero(con))
        else:  # bus row
            b = self.an.machine["bus_interactions"][src.index]
            bid, args = b.get("id"), b.get("args", [])
            if bid == 3 and len(args) >= 2 and isinstance(args[1], int):
                self.declare(args[0])
                self.comment(f"source bus[{src.index}]: VariableRangeChecker "
                             f"(value residue in [0, 2^{args[1]}))")
                q, r = self.quotient(), self.quotient()
                self.assert_(f"(= {self._canon_expr(args[0])} (+ (* {P} {q}) {r}))")
                self.assert_(f"(and (<= 0 {r}) (< {r} {1 << args[1]}))")
                self._scaled_hint(args[0], q, r)
            elif bid == 6:
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

    def add_assumption_for(self, f: Fact, a: Assumption) -> None:
        self.comment(f"named assumption: {a.name} — {a.value}")
        # MEMBUS_BYTE and TS_BOUND *grant* their slot-derived Bound facts
        # outright: the granted claim is asserted so the certificate is
        # (visibly) trivial — the fact rests on the assumption, and this line
        # is where that shows. ACTIVE_SELECTOR fixes the structurally
        # recognized gating column to 1.
        if a in (Assumption.MEMBUS_BYTE, Assumption.TS_BOUND) and isinstance(f, Bound):
            self.assert_(self.claim(f))
        if a is Assumption.ACTIVE_SELECTOR and self.an.active_selector is not None:
            sel = self.an.active_selector
            self.declare(sel)
            self.assert_(f"(= {_smt_sym(sel)} 1)")

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
            row = self.an.mem[f.ordinal]
            self.declare(row.mult)
            v = {"send": 1, "recv": P - 1, "disabled": 0}[f.kind]
            return f"(= (mod {_expr(row.mult)} {P}) {v})"
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
            "; negated claim — must be UNSAT",
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
    """Run one certificate; returns 'unsat' | 'sat' | 'unknown' | 'error:…'."""
    try:
        proc = subprocess.run([z3, "-in", f"-T:{timeout_s}"], input=smt2,
                              capture_output=True, text=True, timeout=timeout_s + 5)
    except (OSError, subprocess.TimeoutExpired) as e:
        return f"error: {e}"
    res = (proc.stdout.strip().splitlines() or ["?"])[-1]
    return res if res in ("sat", "unsat", "unknown") else f"error: {res[:80]}"


def certify_dump(data: Any, mem_id: int = 1, assume_is_valid: bool = True,
                 run: bool = False, out_dir: Path | None = None) -> list[dict]:
    """Certificates for every fact of one dump; optionally write + run them."""
    an = Analysis(data, mem_id, assume_is_valid)
    z3 = find_z3() if run else None
    if run and z3 is None:
        raise ValueError("certify: --run requested but no z3 binary found on PATH")
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
