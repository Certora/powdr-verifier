; rule: choice-quadratic-roots  (roots correct + sound under range)
; Validates BOTH the modular-root computation and conditional soundness.
; instance: x^2-1 over P=7, roots {1,6}, with 0<=x<7 asserted.
; EXPECTED: unsat -- confirms {1,6} are exactly the roots and the exact-eq+bounds
;   form is equivalent to the congruence when x is field-range constrained.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (<= 0 x))
(assert (< x 7))
(define-fun A () Bool (= (mod (- (* x x) 1) 7) 0))
(define-fun B () Bool (and (or (= x 1) (= x 6)) (<= 1 x) (<= x 6)))
(assert (not (= A B)))
(check-sat)
