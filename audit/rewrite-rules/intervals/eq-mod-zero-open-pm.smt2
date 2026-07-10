; rule: eq_mod_zero_open  (simplify, reasoner.py:1046-1049 / 1054-1057)
; contract: rewrite Equals((mod x p),0) -> Equals(x,0) when x's domain is within (-p,p).
; correctness: x ≡ 0 (mod p) and -p < x < p  =>  x == 0.
; INSTANCE: p=7, x in (-7,7).
; CHECK: is (x = 0) implied by (-7 < x < 7 and (mod x 7)=0)?
; EXPECTED: unsat => sound.
(set-logic QF_NIA)
(declare-const x Int)
(assert (< (- 7) x))
(assert (< x 7))
(assert (= (mod x 7) 0))
(assert (not (= x 0)))
(check-sat)
