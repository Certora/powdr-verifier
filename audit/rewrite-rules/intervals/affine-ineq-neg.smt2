; rule: affine_ineq_neg  (_refine_affine_ineq, coeff<0 branch, reasoner.py:336-355)
; contract: sound narrowing -- required: (constraints) => (derived lower bound on sym).
; direction that matters: the derived interval is INTERSECTED into sym's domain and later
;   used to prune/discharge atoms, so it MUST be IMPLIED by the assumptions; if not, models
;   are dropped => UNSAT can be manufactured => false PASS.
;
; INSTANCE: constraint  x <= y  with x in [0,10].  For sym=y, coeff(y)=-1 (neg branch),
;   rest = x with hull [0,10].  sym >= (rest - target_hi)/den, den=1, target_hi=0.
;   A lower bound valid for every feasible rest must use the SMALLEST rest = rest.lo = 0,
;   giving the SOUND bound  y >= 0.
;
; THE BUG (pre-fix): the code used rest.HI (=10) instead of rest.LO (=0):
;     num = h.hi - target_hi = 10 ; lo = ceil(10/1) = 10  =>  narrowed y to [10,+inf).
;   That bound (y >= 10) is NOT implied by (0<=x<=10 and x<=y): x=0,y=0 is a model.
;   Verified end-to-end: `simplify_intervals` on { 0<=x<=10, x<=y, y<=5 } (SAT at x=0,y=0)
;   collapsed an assert to `false` -- a false PASS. See tests/simplify/intervals/
;   test_interval_reasoner_arith.py::test_affine_ineq_neg_multivar_no_false_pass.
;
; THE FIX: use rest.lo (h.lo) in both the None-guard and the numerator, matching the
;   symmetric coeff>0 branch. The rule now derives the sound bound y >= 0.
;
; CHECK (validates the FIXED rule): is the derived bound (y >= 0) implied by
;   (0<=x<=10 and x<=y)?
; EXPECTED: unsat  => rule is SOUND (no model violates the derived bound).
;   (Before the fix this file asserted `(not (<= 10 y))` and z3 returned `sat`, the
;    dropped-model counterexample x=0,y=0.)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 10))
(assert (<= x y))
(assert (not (<= 0 y)))    ; negation of the FIXED derived bound y >= 0
(check-sat)
