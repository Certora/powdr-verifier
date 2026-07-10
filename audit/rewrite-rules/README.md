# Rewrite-rule soundness audit

A rule-by-rule soundness audit of the verifier's simplification / rewrite passes
(both the sympy `src/rewriter/` and the `src/simplify/` pipeline), with a
standalone SMT2 validator per rule so every rule — sound or not — is justified.

**Start with [`FINDINGS.md`](./FINDINGS.md)**: the ranked findings, the triage
note, and the soundness criterion. This README only covers how to reproduce.

## Soundness criterion

The verifier discharges an equivalence VC by checking `assumptions ∧ ¬goal` for
**UNSAT** (UNSAT ⇒ circuits proven equivalent ⇒ **PASS**). So the one
soundness-critical failure of a rewrite `A → B` is turning a **SAT**
(counterexample-bearing) VC into **UNSAT** — a *false PASS*. That happens when a
rewrite **strengthens** an assumption, **drops a model**, or **injects an
unjustified fact**. A rewrite that only weakens/relaxes (adds models) is at worst
a completeness loss, never unsound.

## How the validators are built

Each `<pass>/<rule-slug>.smt2` is self-contained and starts with a header
comment: the rule, its contract (equivalence / equisat / unsat-preserving), what
is checked, and the **expected verdict**. Convention:

- **`unsat` = sound** (no counterexample to the rewrite's contract).
- **`sat` = a counterexample** — the model is a concrete input the rewrite
  mishandles (typically a dropped model → potential false PASS).

Most use a small prime (`P = 7` or `P = 97`) with explicit field-domain
constraints so z3 decides them fast; `*.babybear.smt2` variants use the real
`P = 2013265921` where the prime magnitude matters (may time out).

## Reproduce

```sh
# single validator
z3 -T:15 audit/rewrite-rules/intervals/affine-ineq-neg.smt2

# whole suite (prints file: verdict)
find audit/rewrite-rules -name '*.smt2' | sort | while read f; do
  printf '%-70s %s\n' "$f" "$(z3 -T:15 "$f" 2>&1 | head -1)"
done
```

Timeouts are expected on some `*.babybear.smt2` files — the goal of this pass is
**coverage**, and a reasoning verdict stands on its own (z3 is corroboration).

## Triage (how to read the results)

Two classes, warranting different responses:

- **Non-range logic bugs** — wrong independent of any field invariant; fixes
  should start here. E.g. `intervals/affine_ineq_neg` (a `HI`/`LO` slip, ~one
  token), `intervals/mod_zero_product` (a prime-field disjunction treated as a
  conjunction), `lift_forall` bound-variable capture, `skolem-core` free-var
  strengthening, and the `rewrite_store_eqs` store-decomposition family.
- **`[0,P)` range-invariant class** — unsound only if a solved/rewritten
  variable can leave `[0,P)`. Lower priority: the pipeline does bound checking,
  so the likely gap is that *why* the invariant holds is **undocumented, not
  absent**. A `sat` here is necessary but **not sufficient** — confirming a live
  bug needs an **end-to-end VC** with a genuinely unbounded variable.

## Provenance / caveats

- Audits the **Python** reference. The Rust `rust/simplifier/src/passes/` are
  line-for-line ports, so rule *soundness* is language-independent; a
  Python-vs-Rust divergence check is out of scope here.
- `normalize` findings assume the fix in the modular-inequality PR
  (`modular_ineq_decline` + `lt/le_gcd_keep_sign`); on `main` that fix may still
  be in review.
- Generated 2026-07-10 by a fan-out audit (one agent per pass) + synthesis;
  the three active/unconditional unsound verdicts were re-checked by hand.
