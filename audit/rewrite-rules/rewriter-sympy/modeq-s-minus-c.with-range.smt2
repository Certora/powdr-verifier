; rule: modeq-s-minus-c  (soundness UNDER the range invariant)
; Same rule as modeq-s-minus-c.smt2 with the external invariant 0 <= s < p asserted.
; what is checked: Mod(s - 3, 7)==0  <=>  s == 3   given 0<=s<7
; EXPECTED: unsat  -- with s confined to [0,p) the integer equality is equivalent to the
;   congruence. Confirms the rule is sound precisely when s is field-range constrained.
(set-logic QF_NIA)
(declare-fun s () Int)
(assert (<= 0 s))
(assert (< s 7))
(define-fun A () Bool (= (mod (- s 3) 7) 0))
(define-fun B () Bool (= s 3))
(assert (not (= A B)))
(check-sat)
