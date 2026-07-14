; rule: mod_zero_product  (_refine_from_mod_zero, is_times branch, reasoner.py:521-557)
; contract: sound narrowing.  (u1*...*uk) == 0 (mod p), p prime  =>  SOME factor == 0
;   (mod p) -- a DISJUNCTION.
;
; THE BUG (pre-fix): the code collected, for each unit-affine factor, the root residue of
;   its symbol and then narrowed EACH symbol independently to its root set. Narrowing every
;   symbol at once asserts the CONJUNCTION "factor_1 == 0 AND factor_2 == 0 AND ...", the
;   opposite of the disjunction. For (x*y) mod 7 = 0 with x,y in [0,6] it forced x=0 AND y=0,
;   dropping models like x=0,y=3. A per-variable interval domain simply cannot express a
;   disjunction across variables.
;
; THE FIX: validate the input is a single-variable equation before narrowing. Require EVERY
;   factor to be unit-affine in the SAME symbol s (range-confined to [0,p)); then narrow s to
;   the union of its root residues -- a set-valued domain, which IS a sound disjunction over
;   one variable's values. Any other shape (a second symbol, or an uncharacterized factor
;   that might itself be the zero one) => DECLINE. This preserves the intended target
;   (single-variable flag/root equations like cmp*(cmp-1) == 0) and drops the unsound modes.
;   Verified end-to-end: `simplify_intervals` on { 0<=x<7, 0<=y<7, (x*y) mod 7 = 0, x=3 }
;   (SAT at x=3,y=0) no longer collapses; single-symbol x*(x-3) still narrows x to {0,3}.
;   Tests: tests/simplify/intervals/test_interval_reasoner_arith.py::
;   test_mod_zero_product_multisym_no_false_pass and _single_symbol_still_narrows.
;
; CHECK (the multi-symbol case the fix now DECLINES): is the per-symbol narrowing
;   (x=0 AND y=0) implied by the product fact over the ranges?
; EXPECTED: sat => the conjunction is NOT implied (witness x=0,y=3), which is exactly why
;   the fixed pass must decline rather than narrow. (The fix makes the pass emit nothing
;   here; this file documents the unsoundness of the narrowing it used to perform.)
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= 0 x) (<= x 6)))
(assert (and (<= 0 y) (<= y 6)))
(assert (= (mod (* x y) 7) 0))
(assert (not (and (= x 0) (= y 0))))   ; negation of the pre-fix per-symbol narrowing
(check-sat)
(get-value (x y))
