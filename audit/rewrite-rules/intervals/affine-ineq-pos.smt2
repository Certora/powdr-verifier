; rule: affine_ineq_pos  (_refine_affine_ineq, coeff>0 branch, reasoner.py:324-335)
; contract: sound narrowing (upper bound on positive-coeff symbol).
; INSTANCE: 4 <= x, x + y <= 5.  For y (coeff +1): y <= 5 - x <= 5 - 4 = 1  (uses h.lo).
; CHECK: is (y <= 1) implied by (4<=x and x+y<=5)?
; EXPECTED: unsat => sound.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= 4 x))
(assert (<= (+ x y) 5))
(assert (not (<= y 1)))
(check-sat)
