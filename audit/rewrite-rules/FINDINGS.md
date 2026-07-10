# Powdr verifier rewrite-rule soundness audit — FINDINGS

## Triage note (Arie, 2026-07-10) — read before the ranked list

Two classes of finding here, and they warrant **different** responses:

- **Non-range logic bugs** — wrong independent of any field invariant. These are
  the highest-signal items and where fixes should start: `intervals/affine_ineq_neg`
  (pure-LIA `HI`/`LO` slip, one-token fix), `intervals/mod_zero_product`
  (disjunction treated as conjunction), `lift_forall/cross_assertion_capture`
  (no alpha-renaming), `skolem-core/contribute_free` (unenforced uniform-witness
  invariant), and the `rewrite_store_eqs` store-decomposition family (full `(= A B)`
  over-constrains overwritten slots).
- **`[0,P)` range-invariant class** — rules that are unsound only if a solved/
  rewritten variable can leave `[0,P)`. **De-prioritised.** The pipeline does bound
  checking and this issue is known, so the likely reality is that *why* the
  invariant holds is **undocumented, not absent**. A `sat` on a synthetic
  small-prime validator here is necessary but **not sufficient** — calling one of
  these a *live* bug requires an **end-to-end VC** exhibiting a genuinely unbounded
  variable. Treat as "prove/document the invariant," not "fix a live bug":
  `demod/eqmod-zero-solve`, the sympy `roots_with_range` rules (U1/U2),
  `bounds/inject-field-range`, and the dormant `modeq-*` rules.

The ranking below is by the audit's raw severity criterion; apply this triage on
top of it when choosing what to act on.

## Overview

This is a rule-by-rule soundness audit of the powdr verifier's simplification /
rewrite passes. The verifier discharges an equivalence VC by checking a formula
`Phi = assumptions ∧ ¬goal` for **UNSAT** (UNSAT ⇒ circuits proven equivalent ⇒
**PASS**). The one soundness-critical failure mode is therefore a rewrite that
turns a **SAT** (counterexample-bearing) VC into **UNSAT** — a *false PASS*.
Concretely that means a rewrite that **strengthens** an assumption, **drops a
model**, or **injects an unjustified fact**. Rewrites that only weaken/relax the
VC (add models) are at worst a completeness loss (*false FAIL*), never unsound.
Each rule was judged by that criterion and, where a semantic transform exists,
backed by a standalone z3 validator (small prime `P=7` or `P=97`, with real
BabyBear `P=2013265921` variants where the prime magnitude matters). Two active,
unconditional unsound rules were found in `demod` and `intervals`; a family of
four unsound array-decomposition rules in `rewrite_store_eqs` (reachable only
with distinct symbolic bases); one dormant unsound rule in the sympy rewriter;
and a cluster of conditional/latent findings marked *uncertain*.

### Summary table

| Verdict | Count | Notes |
|---|---:|---|
| **unsound** | 8 | 3 active+unconditional; 4 active-but-reachability-open; 1 dormant |
| **uncertain** | 12 | conditional soundness, latent gaps, or unenforced invariants |
| **sound** | 41 | verified by z3 and/or algebra |
| **not-applicable** | 9 | pure plumbing / delegation, no semantic transform |
| **total rules** | 70 | across 18 passes |

**Passes covered (18):** rewriter-sympy, normalize, bitwise, mod_inv, demod,
bounds, intervals, nnf, lift_forall, flatten_outer_array, define_inner_array,
solve_eqs, solve_store_eqs, rewrite_store_eqs, witness, domain_probe,
skolem-core, skolem-aux, external-solvers.

Verdict counts by pass (unsound / uncertain / sound / n-a):
rewriter-sympy 1/5/3/2 · normalize 0/1/5/0 · bitwise 0/0/13/0 · mod_inv 0/0/2/0 ·
demod 1/0/6/0 · bounds 0/1/0/1 · intervals 2/2/6/0 · nnf 0/0/6/0 ·
lift_forall 0/1/1/0 · flatten_outer_array 0/0/5/0 · define_inner_array 0/1/4/1 ·
solve_eqs 0/0/2/0 · solve_store_eqs 0/0/2/0 · rewrite_store_eqs 4/0/4/0 ·
witness 0/0/1/1 · domain_probe 0/0/1/0 · skolem-core 0/1/4/0 ·
skolem-aux 0/0/5/2 · external-solvers 0/1/0/1.

---

## Ranked findings

### UNSOUND (most severe first)

Ranking principle: **active + unconditional + no guard** ranks above
**active-but-reachability-open** above **dormant**.

---

#### 1. `demod` / `eqmod-zero-solve` — ACTIVE, unconditional, no guard
- **Contract:** unsat-preserving · **Verdict:** unsound
- **Crux:** `(= (mod (a*x+b) p) 0)` → `(= x val)` with `val = (-b)*a⁻¹ mod p`,
  applied **unconditionally at every `Equals` node**, with **no range guard on
  `x`**. The original constrains `x` only *modulo p* (the whole residue class
  `{val, val±p, …}`); the rewrite pins `x` to the single representative in
  `[0,p)`. That is a **strengthening** → drops models → can turn a SAT VC into
  UNSAT = false PASS. The modular-inverse arithmetic itself is correct; the sin
  is dropping the modulus. Sibling `mod-elim-by-range` in the *same file* is
  carefully range-guarded — this path is not. A unit test exercises it on an
  unbounded `x`, so the gap is real, not hypothetical. Sound **only** under an
  external `0 ≤ x < p` invariant the pass neither checks nor requires.
- **Validators:** `demod/eqmod-zero-solve.smt2` → **sat** (witness `x=191=94+97`,
  lost counterexample); `demod/eqmod-zero-solve-withrange.smt2` → **unsat** (with
  `0≤x<p` the two forms are equivalent — soundness is conditional on the invariant).

#### 2. `intervals` / `affine_ineq_neg` — ACTIVE, untested, pure-LIA bug
- **Contract:** unsat-preserving · **Verdict:** unsound
- **Crux:** the `coeff<0` branch of `_refine_affine_ineq` (reasoner.py:336–348)
  derives `x`'s lower bound from `rest.HI` instead of the sound `rest.LO`. For
  `coeff<0`, a value is feasible iff the *smallest* `rest` supports it, so the
  projection must use `rest.LO`. Using `rest.HI` over-tightens whenever ≥2
  variables are involved, excluding real models. The sibling `coeff>0` branch
  and `affine_eq` use the correct endpoint — the asymmetry is the tell. The
  over-tight bound is then injected / used to prune atoms → SAT→UNSAT false PASS.
  Existing tests only use single-var/constant-rest cases where `lo==hi` masks it.
  Field-independent (pure LIA).
- **Validator:** `intervals/affine_ineq_neg.smt2` → **sat** (model `x=0,y=0`
  satisfies `0≤x≤10 ∧ x≤y` but violates the derived `y≥10`).

#### 3. `intervals` / `mod_zero_product` — ACTIVE, untested, OR-treated-as-AND
- **Contract:** unsat-preserving · **Verdict:** unsound
- **Crux:** `_refine_from_mod_zero` (reasoner.py:519–549) handles
  `(= (mod (u1*…*uk) P) 0)` by intersecting **each** factor's symbol with its
  own zero-residue — i.e. it turns the prime-field **disjunction** (*some*
  factor ≡ 0) into a **conjunction** (*all* factors ≡ 0). For `(mod (x*y) P)=0`
  with canonical `x,y` it forces `x=0 ∧ y=0`, deleting valid models like
  `x=0,y=4`. Fires on canonically-bounded field variables (the norm) with no
  guard restricting to the sound single-symbol case (`x*(x-3)`). Untested.
- **Validator:** `intervals/mod_zero_product.smt2` → **sat** (model `x=0,y=4`).

#### 4–7. `rewrite_store_eqs` / four store-decomposition rules — unsound for distinct bases
- **Rules:** `store-store-same-idx`, `store-store-diff-const-idx`,
  `store-nonstore`, `nonstore-store`
- **Contract:** equivalence · **Verdict:** unsound
- **Crux (shared defect):** decomposing an array-store equality, the reducer
  emits `base_eq = (= A B)` (full array equality) for the two bases. But a store
  equality only requires the bases to agree **off** the overwritten index(es) —
  the overwritten slots are free. Forcing `A[k]=B[k]` too is a **strict
  strengthening** → drops models → SAT→UNSAT false PASS (same class as the known
  normalize `a<b` bug). **Exact and sound when the two bases are the identical
  FNode** (`base_eq` collapses to `True`) — the only case the module docstring
  claims and the unit tests exercise. The docstring's assertion that the residual
  `(= base_a base_b)` for distinct bases is exact is **wrong**. Reachability
  hinges on whether two distinct symbolic base arrays survive into this pass
  after `solve_store_eqs` inlining (plausible when two circuits' memory chains
  bottom out at different base/const arrays) — **open follow-up**.
- **Validators (all → sat, each a dropped model):**
  `rewrite_store_eqs/store-store-same-idx.smt2`,
  `…/store-store-diff-const-idx.smt2`, `…/store-nonstore.smt2`,
  `…/nonstore-store.smt2`.
- Note: the index-equality helper `canon-arith-moddist` these rules depend on is
  **sound** (mod idempotence/distributivity verified at P=97 **and** real BabyBear).

#### 8. `rewriter-sympy` / `modeq-c-plus-negs-raw-constant` — DORMANT latent bug
- **Contract:** equivalence · **Verdict:** unsound
- **Crux:** `rewrite_mod_equality` case 5, `Mod(c+(P-1)*s,p)==0 → Eq(s,c)`,
  returns the constant `c` **raw/unreduced** (should be `Eq(s, Mod(c,p))`),
  inconsistent with sibling cases 1/2 which reduce it. For `c≥p` this manufactures
  UNSAT **even when the field-range invariant `0≤s<p` holds** — so unlike the
  other integer-vs-congruence findings it is not merely a range issue.
  **Harmless today only because `rewrite_mod_equality` is dormant** (imported but
  not wired into `REWRITES_SYMPY`).
- **Validator:** `rewriter-sympy/modeq-c-plus-negs-bug.smt2` → **sat** (with
  `0≤s<7` asserted, `s=0` satisfies `Mod(7+6s,7)=0` but `Eq(s,7)` is false).

---

### UNCERTAIN (conditional soundness / latent / unenforced invariant)

Highest-value first (active and/or reachable).

#### U1. `rewriter-sympy` / `choice-solved-roots-range` — ACTIVE key finding
- **Contract:** equivalence · **Crux:** `Mod(e,p)=0` with every factor linear in
  one symbol `x` → exact integer equalities `x==r` **plus** `min≤x≤max`, dropping
  the modulus. Over ℤ this is **strictly stronger** than the congruence (it
  forbids `x=r+kp`), so a genuine equivalence **only** when `x` is independently
  constrained to `[0,p)`. That `[0,p)` axiom is injected by `simplify_bounds` only
  for symbols named `@<digits>`; this rule never checks it. Sound for the intended
  targets (range-checked boolean/flag columns, e.g. `cmp*(cmp-1)=0`); latent
  false-PASS risk for any solved variable lacking the axiom. One of only **two
  live rules** in the sympy rewriter.
- **Validators:** `choice-solved-roots-range.smt2` → **sat** (x=8 for
  `Mod(x*(x-1),7)=0`); `…with-range.smt2` → **unsat**.

#### U2. `rewriter-sympy` / `choice-quadratic-roots` — ACTIVE
- **Contract:** equivalence · **Crux:** inherits U1's conditional soundness (reuses
  `roots_with_range`). Root computation itself (Tonelli-Shanks `_mod_sqrt`) was
  verified correct/complete at P=7; that correctness is load-bearing — a wrongly
  dropped root would strengthen further.
- **Validators:** `choice-quadratic-roots.smt2` → sat; `…with-range.smt2` → unsat.

#### U3. `bounds` / `inject-field-range-axiom` — ACTIVE, whole-pass
- **Contract:** unsat-preserving · **Crux:** prepends `0≤x<P` for every free Int
  symbol named `@<digits>`. This is domain-hypothesis **injection**, not a rewrite;
  monotone for UNSAT, but the dangerous SAT→UNSAT direction is exactly what
  injecting a bound does. Sound **iff** the naming convention reliably identifies
  canonical field columns in `[0,P)`; unsound for any matched symbol that can be
  negative or `≥P`. Correctly declines to inject under quantifiers.
- **Validators:** `bounds/range-axiom-adds-info.smt2` → sat (bound non-redundant,
  x=-94); `…sat-to-unsat.smt2` → sat then unsat (false-PASS flip if invariant
  violated); `…sound-under-invariant.smt2` → unsat.

#### U4. `intervals` / `meta-eval_bool-inject_bounds-quantifier_injection`
- **Contract:** other · **Crux:** the domain-consumption machinery (atom pruning,
  root/quantifier bound injection) is sound **given sound domains**, but it consumes
  domains from `affine_ineq_neg` and `mod_zero_product` — so it becomes **unsound in
  composition** with findings #2 and #3. No standalone validator (plumbing).

#### U5. `skolem-core` / `contribute_free` — the one strengthening skolem path
- **Contract:** unsat-preserving · **Crux:** the **only** skolem path that does
  not append a disjunct to a positive forall — it inserts a **top-level**
  `(assert (= v e))` on a *free* variable, which is a **strengthening**. Sound only
  if `e` is a uniform witness (`v` genuinely unconstrained by, or determined by,
  the remaining assertions); the code **assumes** this without checking, and
  `swap_sym` can silently build a mixed before/after witness. Leans sound in
  practice given the project invariant that bus matching is by (key,timestamp) not
  data, but relies on an **unenforced** invariant. Recommended hardening focus.
- **Validators:** `skolem-core/contribute-free-unsound-general.smt2` → sat (false
  PASS when `v` constrained to `d≠e`); `…sound-when-unconstrained.smt2` → unsat.

#### U6. `lift_forall` / `cross_assertion_capture` — freshness/variable-capture
- **Contract:** equisat · **Crux:** the one-point lift is sound, but the shared
  `LiftForallWalker` keys `self.lifted` by the qvar FNode with no alpha-renaming.
  Two forall assertions reusing the same bound-var symbol (pySMT interns bound
  vars; skolem pins are same-name column vars) get conflated — the earlier pin is
  overwritten, both bodies forced onto the last pin's value → SAT→UNSAT possible.
  Reachability depends on whether the encoder reuses a bound-var name across
  surviving forall assertions. Fix: alpha-rename / fresh global per lift, or abort
  on collision.
- **Validator:** `lift_forall/cross_assertion_capture.smt2` → sat (divergence
  witness `e1=0,e2=1`).

#### U7. `define_inner_array` / `const_to_default` — latent, parser-unreachable
- **Contract:** equisat · **Crux:** `_build_body` returns only
  `array_value_default()` for an `ARRAY_VALUE` literal, **dropping the
  assigned-values map**. If a defining RHS is an `ARRAY_VALUE` with a non-empty
  map, the macro becomes constant → SAT→UNSAT false PASS. Confirmed via the pysmt
  parser that this node shape is **not** produced from raw SMT parsing (store
  chains stay `ARRAY_STORE`; `(as const)` parses to an empty-map `ARRAY_VALUE`), so
  latent unless an upstream pysmt transform materializes such a node.
- **Validator:** `define_inner_array/const_default_drops_assignments.smt2` → sat.

#### U8. `normalize` / `modular_eq_out_of_range_const` — latent, not currently reachable
- **Contract:** equivalence · **Crux:** `(= (mod a P) C)` → `(a == C mod P)` accepts
  **any** Int constant `C` with no `0≤C<P` guard. For `C` outside `[0,P)` the
  original is unsatisfiable while the rewrite is satisfiable — non-equivalence,
  polarity-unsafe for the full-DAG walker. Not reachable today (encoders only emit
  RHS `Int(0)`), so `field_eq_monic` is sound as used. Recommend an explicit
  `0≤C<P` (or RHS==0) guard.
- **Validator:** `normalize/modular_eq_out_of_range_const.smt2` → sat (C=100, P=97).

#### U9. `external-solvers` / `cvc5-preprocess-only-extract` — disabled/debug
- **Contract:** equisat · **Crux:** text-slices cvc5's `pre-theory-preprocess`
  trace dump. Currently a no-op (hardcoded nonexistent binary paths). Safe failure
  modes dominate (dropped asserts weaken; malformed slices crash loudly). Residual
  unverified hazard: a mis-sliced region parsing as a *strengthened* assert.
  Uncertain because unexercisable here. No validator (plumbing).

#### U10–U12. Dormant / disabled integer-vs-congruence rules (rewriter-sympy)
- `modeq-s-minus-c`, `modeq-s-minus-s2` (both **dormant**), and
  `rewrite-mod-drop-symbol` (`Mod(x,p)→x`, **disabled** — MOD entry commented out).
  All are the same class: exact integer equality/value is strictly stronger than
  the congruence, sound only under a `[0,p)` invariant. **No live impact.**
  Validators: `modeq-s-minus-c.smt2` sat / `…with-range.smt2` unsat;
  `modeq-s-minus-s2.smt2` sat; `rewrite-mod-drop-symbol.smt2` sat.

---

### SOUND (verified) — grouped

- **normalize (5):** `field_eq_monic` (unit-multiply preserves mod-P zero set;
  verified single-var + multivar/deg-2), `eq_gcd_rescale`, `lt_gcd_keep_sign`,
  `le_gcd_keep_sign` (the **fix** for the prior gcd sign-flip — divide by positive
  gcd, never negate), `modular_ineq_decline` (the pass now **declines** modular
  inequalities — the fix for the known bug; validator sat confirms the old rewrite
  was unsound).
- **bitwise (13):** all constant-folds and byte-guarded lemmas; mask/complement
  lemmas correctly require and carry the `0≤x≤255` guard. All 13 z3-unsat.
- **mod_inv (2):** `def_fold`, `fallback_axiom` — sound in the no-false-PASS
  direction, resting on BabyBear primality (composite-modulus sensitivity check
  sat, as expected).
- **demod (6):** `normalize-arith-under-mod`, `mod-const-fold` (latent negative-
  modulus gap from `mc!=0` vs `mc>0`, believed unreachable), `mod-push-ite`,
  `mod-elim-by-range` (correctly range-guarded), `self-mod-witness`,
  `range-facts-bounds`.
- **intervals (6):** `affine_ineq_pos`, `affine_eq`, `mod_unwrap_ineq`,
  `mod_ineq_tautology`, `mod_zero_unique_multiple`, `eq_mod_zero_open_pm`.
- **nnf (6):** implies-elim, De Morgan (and/or), not-not, flatten, and the
  quantifier/ITE no-push (incomplete but sound — never performs the risky
  ∀↔∃ duality).
- **rewriter-sympy (3):** `choice-disjunction` (prime ⇒ integral-domain
  zero-product), `choice-no-roots-false`, `normalize-coeff-reduction`.
- **flatten_outer_array (5):** incl. the soundness-critical `eq-expand-K`
  (relaxation ⇒ no false PASS; completeness gap closed by fail-closed survivor
  check).
- **define_inner_array (4):** store_to_ite, alias_to_forward, array_eq_pointwise,
  select_to_call.
- **solve_eqs (2), solve_store_eqs (2):** one-point / destructive-equality
  elimination — structural SMT `=`, not modular; both soundness guards enforced.
- **rewrite_store_eqs (4):** eq-refl, select-over-store, constarray-eq,
  canon-arith-moddist.
- **witness (1):** expanded-witness universal instantiation (weakening in positive
  position; latent polarity caveat noted).
- **domain_probe (1):** probe-exclude (injected disequality is entailed via
  subset-monotonicity).
- **skolem-core (4) + skolem-aux (5):** every pin routes through `SkolemMap.pin`
  → disjunct appended to a **positive** forall (guaranteed by `nnf:skolem:lift`
  ordering) = pure weakening, sound for any witness; witness correctness is
  completeness-only.

*(not-applicable: conversion/serialization/detection plumbing and external-solver
delegation — 9 rules; `external-solvers/z3-tactic-simplify-splice` is sound
contingent on trusting z3's tactic engine.)*

---

## Review queue (look here first)

1. **`demod` / `eqmod-zero-solve`** — active, unconditional, no range guard;
   the clearest live false-PASS risk. Decide: add a `0≤x<p` guard (mirror the
   sibling `mod-elim-by-range`), or prove every reachable solved symbol is
   range-bounded.
2. **`intervals` / `affine_ineq_neg`** — one-line fix (`rest.HI` → `rest.LO` in
   the `coeff<0` branch), active, untested, pure-LIA. Add a ≥2-variable test.
3. **`intervals` / `mod_zero_product`** — restrict to the single-symbol case or
   emit the disjunction; active, untested.
4. **`rewrite_store_eqs` store-decomposition family (4 rules)** — resolve the
   **reachability** question: can two distinct symbolic base arrays survive
   `solve_store_eqs` into this pass? If yes, the `(= A B)` `base_eq` is a live
   false-PASS; fix to "agree off the overwritten indices."
5. **`skolem-core` / `contribute_free`** — highest-value uncertain: the only
   strengthening skolem path, relies on an unenforced uniform-witness invariant;
   `swap_sym`'s silent fallback can mix before/after symbols. Add a check that
   `v` is unconstrained outside the removed constraints, or prove `e` is implied.
6. **`bounds` / `inject-field-range-axiom`** — audit the `@<digits>` naming
   convention: confirm every match is a canonical field column in `[0,P)`.
7. **`lift_forall` / `cross_assertion_capture`** — alpha-rename bound vars or
   abort on symbol collision; cheap defensive fix against a plausible encoder
   pattern.
8. **`rewriter-sympy` / `choice-solved-roots-range` + `choice-quadratic-roots`**
   — active; confirm every solved variable receives the `[0,p)` axiom, or have
   the rule assert/require it.

Dormant/disabled unsound rules (`modeq-c-plus-negs-raw-constant` and siblings)
are lower priority but should be **fixed or deleted** before anyone wires
`rewrite_mod_equality` / `rewrite_mod` into the active maps.

---

## Cross-reference: the known normalize modular-inequality bug

Durable note: `durable/normalize-inequality-mod-unsound.md`. That bug —
`_NormalizeWalker.walk_lt`/`walk_le` rewriting a modular `a<b` into
`(mod (a-b) P) < 0`, which is **unconditionally false** (Euclidean mod lands in
`[0,P)`), making the whole VC vacuously UNSAT — plus its latent `_rescale_gcd`
sign-flip sibling.

**Audit status of that bug:** the `normalize` pass now carries
`modular_ineq_decline` — it **returns None / keeps the original relation** for
modular inequalities (verdict **sound**; the validator's sat result confirms the
old rewrite was unsound and the decline is required). The sign-flip is fixed by
`lt_gcd_keep_sign` / `le_gcd_keep_sign` (divide by the **positive** gcd, never
negate; both **sound**). **Both halves of the durable bug are confirmed fixed.**

**Sibling issues in the same class** (integer-vs-modular / order- or
value-strengthening that drops models and can manufacture UNSAT). The audit found
several, so the class is **not** confined to `normalize.py`:

- **`demod` / `eqmod-zero-solve` (unsound, active):** drops the modulus and pins
  a congruence class to its `[0,p)` representative — the same "mod not preserved"
  defect, on the equality path, live.
- **`rewrite_store_eqs` store family (unsound):** explicitly flagged by the
  auditor as "the same failure class as the known normalize a<b bug"
  (strengthening removes models → SAT→UNSAT).
- **`rewriter-sympy` roots_with_range (U1/U2, active uncertain)** and the dormant
  `modeq-*` / `rewrite-mod-drop-symbol` (U10–U12): the integer-equality-vs-
  congruence strengthening, sound only under a `[0,p)` invariant.
- **`normalize` / `modular_eq_out_of_range_const` (U8):** the residual
  out-of-range-constant gap on the *equality* path, latent.

Net: the specific inequality bug is fixed, but its underlying class — treating a
modular/relational fact as an exact integer fact without a range invariant — recurs
across `demod`, `rewrite_store_eqs`, and the sympy rewriter. The review queue is
prioritized accordingly.
