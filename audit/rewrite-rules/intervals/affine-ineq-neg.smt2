; rule: affine_ineq_neg  (_refine_affine_ineq, coeff<0 branch, reasoner.py:336-348)
; contract: sound narrowing  -- required: (constraints) => (derived lower bound on sym)
; direction that matters: the derived interval is INTERSECTED into sym's domain and later
;   emitted as an injected root/quantifier bound conjunct, so it must be IMPLIED by the
;   assumptions; if it is not, models are dropped => UNSAT can be manufactured => false PASS.
; INSTANCE: constraint  x <= y  with x in [0,10].  For sym=y, coeff(y)=-1 (neg branch).
;   Code computes num = h.hi - target_hi = 10 - 0 = 10, den = 1, lo = ceil(10/1) = 10,
;   and narrows y to [10, +inf).  (Verified empirically: y domain = [10,oo).)
;   Sound bound is y >= min(x) = 0, i.e. y in [0,+inf).
; CHECK: is the derived bound (y >= 10) implied by (0<=x<=10 and x<=y)?
; EXPECTED: sat  => rule is UNSOUND. A sat model (e.g. x=0,y=0) satisfies the assumptions
;   but violates the derived bound y>=10, proving the narrowing drops feasible models.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 10))
(assert (<= x y))
(assert (not (<= 10 y)))   ; negation of the derived bound y>=10
(check-sat)
(get-value (x y))
