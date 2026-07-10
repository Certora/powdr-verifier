# Powdr verifier rewrite-rule soundness audit — FINDINGS

## Triage note (Arie, 2026-07-10) — read before the ranked list

Two classes of finding here, and they warrant **different** responses:

- **Non-range logic bugs** — wrong independent of any field invariant. These are
  the highest-signal items and where fixes should start: `intervals/affine_ineq_neg`
  (pure-LIA `HI`/`LO` slip — FIXED #36), `intervals/mod_zero_product`
  (disjunction treated as conjunction — FIXED #37), and the `rewrite_store_eqs`
  store-decomposition family (full `(= A B)` over-constrains overwritten slots).
  (`skolem-core/contribute_free` **resolved sound**, see U5 — standard skolemization,
  machine-checked by `../proofs/ZkvmProofs/Skolem.lean`; `lift_forall/cross_assertion_capture`
  **deprioritized**, see U6 — bound vars are all distinct so the collision can't fire.)
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
| **uncertain** | 9 | conditional soundness, latent gaps (was 12; contribute_free→sound U5, lift_forall→n/a U6, bounds→sound U3) |
| **sound** | 44 | verified by z3, algebra, a skolemization proof (contribute_free), or a domain invariant (bounds: columns are field-valued) |
| **not-applicable** | 9 | pure plumbing / delegation, no semantic transform |
| **total rules** | 70 | across 18 passes |

**Passes covered (18):** rewriter-sympy, normalize, bitwise, mod_inv, demod,
bounds, intervals, nnf, lift_forall, flatten_outer_array, define_inner_array,
solve_eqs, solve_store_eqs, rewrite_store_eqs, witness, domain_probe,
skolem-core, skolem-aux, external-solvers.

Verdict counts by pass (unsound / uncertain / sound / n-a):
rewriter-sympy 1/5/3/2 · normalize 0/1/5/0 · bitwise 0/0/13/0 · mod_inv 0/0/2/0 ·
demod 1/0/6/0 · bounds 0/0/1/1 · intervals 2/2/6/0 · nnf 0/0/6/0 ·
lift_forall 0/0/2/0 · flatten_outer_array 0/0/5/0 · define_inner_array 0/1/4/1 ·
solve_eqs 0/0/2/0 · solve_store_eqs 0/0/2/0 · rewrite_store_eqs 4/0/4/0 ·
witness 0/0/1/1 · domain_probe 0/0/1/0 · skolem-core 0/0/5/0 ·
skolem-aux 0/0/5/2 · external-solvers 0/1/0/1.

---

## Ranked findings

### UNSOUND (most severe first)

Ranking principle: **active + unconditional + no guard** ranks above
**active-but-reachability-open** above **dormant**.

---

#### 1. `demod` / `eqmod-zero-solve` — ACTIVE, unconditional, no guard — **STATUS: REQUIRES RESOLUTION**
- **Contract:** unsat-preserving · **Verdict:** unsound (range-class) · **Decision
  (Arie, 2026-07-10): must be resolved.** On the default path on BOTH backends
  (`demod` runs 4× in `DEFAULT_TACTIC`; ported to Rust `demod.rs`), so if the `[0,p)`
  invariant ever fails for an `x` this fires on, it is a live false PASS. Resolve by
  one of: (1) emit the congruence `(= (mod x p) val)` (always sound), (2) guard on a
  proven `0≤x<p` (mirror the sibling `mod-elim-by-range`), or (3) an end-to-end VC
  probe proving every solved `x` is range-bounded (→ document invariant, downgrade).
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

#### U1. `rewriter-sympy` / `choice-solved-roots-range` — **OFF DEFAULT PATH (Python rewriter not run)**
- **Scope (2026-07-10):** the Python sympy rewriter (`src/rewriter/`) is **not** on
  the default path — with `--default-executor r` (ed33584), the `rewrite` token
  dispatches to Rust `rewrite.rs`, not `simplify_rewrite`. So U1/U2 are latent for the
  Python backend only. **The live equivalent is Rust `rewrite.rs::roots_with_range`**,
  which emits `(x=v1 ∨ … ∨ x=vk) ∧ min≤x≤max` — same range-class dependency (exact
  root values, not a congruence). Audit the Rust rule alongside `demod` (#1); the
  Python findings below are the reference, not the active surface.
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

#### U3. `bounds` / `inject-field-range-axiom` — RESOLVED: SOUND
- **Verdict (2026-07-10, revised): sound** (Arie). Injects `field_symbol(sym) =
  (0 ≤ sym ∧ sym < P)` (smt/utils.py:264) for Int **symbols** named `@<digits>` —
  never terms (`sym.is_symbol()` gate), never inside quantifiers (declines). All
  circuit **columns are field-valued ∈ [0,P)** by construction; only compound *terms*
  over them can exceed P, and terms are not symbols. So every injected bound is a
  **true** fact → sound. Injecting a true fact for a subset can only remove spurious
  (non-field) integer models, never a real counterexample.
- **Coverage nuance (empirical, dump `…2099512_002→003.soundness`): only 262 of 838
  Int symbols match `@<digits>`.** The other 576 (`after-memory-*-data*`, `*-mult`,
  `-2`/`-new` bus vars) get **no** range axiom. Harmless for `bounds` (skipping =
  completeness), but it means the `[0,P)` invariant is **NOT uniformly present** in
  the SMT — `bounds` underwrites the APC columns, not the memory-bus data/mult vars.
- **Implication for the range cluster:** `demod/eqmod-zero-solve` and the Rust roots
  rule fire on *any* single symbol with no naming filter; if they hit a non-`@<digits>`
  bus var, no `[0,P)` fact exists for it. → prefer the **congruence rewrite** for demod
  (#1), which is sound regardless of whether the var was axiomatized.
- **Validators:** `bounds/range-axiom-adds-info.smt2` (bound non-redundant),
  `…sat-to-unsat.smt2` / `…sound-under-invariant.smt2` — these only show that *if* a
  matched symbol could exceed P the injection would be unsound; that antecedent does
  not hold for field columns.

#### U4. `intervals` / `meta-eval_bool-inject_bounds-quantifier_injection`
- **Contract:** other · **Crux:** the domain-consumption machinery (atom pruning,
  root/quantifier bound injection) is sound **given sound domains**, but it consumes
  domains from `affine_ineq_neg` and `mod_zero_product` — so it becomes **unsound in
  composition** with findings #2 and #3. No standalone validator (plumbing).

#### U5. `skolem-core` / `contribute_free` — RESOLVED: sound skolemization (NOT a soundness finding)
- **Verdict (2026-07-10, revised): sound.** Downgraded from "leans unsound" after
  review with Arie. `contribute_free` inserts a top-level `(assert (= v e))` pinning
  a free `diff_val`/`diff_marker` var to a Skolem term `e`. This is **standard
  skolemization**, not an unjustified strengthening: it is the canonical
  refutation form `∃x,y. y = sk x ∧ ¬φ` from the machine-checked theorem
  `flip_quant` in `../proofs/ZkvmProofs/Skolem.lean`
  (`(∃ sk, ¬∃ x y, y = sk x ∧ ¬φ) ↔ ¬∃ x, ∀ y, ¬φ`). The forward direction gives
  soundness for **any** Skolem term `sk` (a real counterexample is bad for all `y`,
  hence at `y = sk x`), so the heuristic choice of `e` — computed by finding a
  satisfying assignment / prefix-swapping the before-side witness — is a
  **completeness** concern, never soundness.
- **Standing premise (design intent, not an open risk):** soundness holds because
  these vars occupy the skolemizable position — either universally closed in the
  obligation (`flip_quant`'s `∀y`; then any `e` sound), or functionally determined
  by the surviving constraints (then the recovered value is the unique one). Arie
  confirms the encoding intent. The earlier "must be an implied/forced value"
  framing only applies to the free-existential-non-unique case, which is not the
  design here.
- **Residual (non-soundness):** `swap_sym`'s silent fallback (returns the un-swapped
  symbol when the counterpart isn't declared) can pick a worse Skolem term — a
  **completeness** wart, not a soundness bug (any `sk` is sound).
- **Validators:** `skolem-core/contribute-free-unsound-general.smt2` (sat) only
  demonstrates the hazard for a hypothetical free-existential-non-unique var; it is
  **not** exhibited by this pass under the skolemization argument above.

#### U6. `lift_forall` / `cross_assertion_capture` — DEPRIORITIZED: precondition doesn't hold
- **Verdict (2026-07-10, revised): does not apply.** The concern was that
  `LiftForallWalker` keys `self.lifted` by the qvar FNode with no alpha-renaming, so
  two foralls **reusing the same bound-var symbol** would conflate pins → SAT→UNSAT.
  Arie confirms the encoder emits **all bound variables distinct**, so the collision
  precondition never arises. Not a live issue.
- **Residual (optional, non-soundness):** an alpha-rename / abort-on-collision guard
  would make the pass robust if the distinctness invariant ever changed — a cheap
  defensive check, **not needed now**.
- **Validator:** `lift_forall/cross_assertion_capture.smt2` (sat) only demonstrates
  the hypothetical collision; it is not reachable given distinct bound vars.

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

"Active" = on the default pipeline (Rust backend running `DEFAULT_TACTIC`:
bitwise, bounds, demod, domain_probe, isqf, lift, mod_inv, nnf, normalize, rewrite,
skolem, witness). `intervals`, `*_store_eqs`, `solve_eqs`, `flatten/define_array`,
`cvc5` are **opt-in and absent from Rust** → lower priority regardless of verdict.

**Done / resolved:**
- ✅ **`intervals` / `affine_ineq_neg`** — FIXED (`rest.HI`→`rest.LO`), PR #36.
- ✅ **`intervals` / `mod_zero_product`** — FIXED (single-var guard, decline else), PR #37.
- ✅ **`skolem-core` / `contribute_free`** — RESOLVED as **sound** (standard
  skolemization, machine-checked `../proofs/ZkvmProofs/Skolem.lean`); see U5.
- ✅ **`lift_forall` / `cross_assertion_capture`** — DEPRIORITIZED (see U6): bound
  vars are all distinct, so the collision precondition never holds. Optional
  defensive check only.

**Open — active pass, `[0,P)` range class (find end-to-end VC OR document invariant):**
1. **`demod` / `eqmod-zero-solve`** — ⚠️ **REQUIRES RESOLUTION** (Arie). The only
   hard-unsound verdict on an active pass (default path, both backends); drops the
   modulus. Resolve via congruence rewrite / range guard / end-to-end probe (see
   finding #1).
2. ✅ **`bounds` / `inject-field-range-axiom`** — RESOLVED sound (U3): injects a true
   `0≤x<P` for `@<digits>` field columns only, symbols-not-terms, declines under
   quantifiers. Nuance: only 262/838 Int symbols are `@<digits>` — bus data/mult vars
   are un-axiomatized, so it does NOT uniformly supply `[0,P)` for #1.
3. **`rewrite.rs` roots (Rust)** — the Python `rewriter-sympy` roots (U1/U2) are
   **off the default path**; the live equivalent is Rust `rewrite.rs::roots_with_range`
   with the same `[0,p)` dependency. Audit the Rust rule; confirm every solved var
   gets the `[0,p)` axiom, or have it require the congruence.

**Open — not on default path (fix before enabling):**
4. **`rewrite_store_eqs` store-decomposition (4 rules)** — resolve reachability
   (distinct symbolic bases surviving `solve_store_eqs`), then fix `base_eq` to
   "agree off the overwritten indices." Opt-in + no Rust port.
5. Dormant/disabled sympy `modeq-c-plus-negs-raw-constant` and siblings — fix or
   delete before anyone wires `rewrite_mod_equality` / `rewrite_mod` into the active maps.

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
