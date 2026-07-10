; rule: choice-no-roots-false (bounded decidable variant)
; Mod(x^2+1,7)==0 value depends only on x mod 7; ranging x over [0,7) covers all classes.
; EXPECTED: unsat (sound: no root, FALSE is correct).
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (and (<= 0 x) (< x 7)))
(assert (= (mod (+ (* x x) 1) 7) 0))
(check-sat)
