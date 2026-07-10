; rule: choice-solved-roots-range  (soundness UNDER the range invariant)
; Same rule as choice-solved-roots-range.smt2, but now the external invariant
;   0 <= x < p  is asserted (as simplify_bounds would add for an '@N' column).
; what is checked: Mod(x*(x-1),7)==0  <=>  ((x=0 or x=1) and 0<=x<=1)   given 0<=x<7
; EXPECTED: unsat  -- with x confined to [0,p) the exact-equality + bounds form IS
;   equivalent to the congruence, so the rule is sound *precisely when* the solved
;   variable is field-range constrained. Confirms the soundness is CONDITIONAL.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (<= 0 x))
(assert (< x 7))
(define-fun A () Bool (= (mod (* x (- x 1)) 7) 0))
(define-fun B () Bool (and (or (= x 0) (= x 1)) (<= 0 x) (<= x 1)))
(assert (not (= A B)))
(check-sat)
