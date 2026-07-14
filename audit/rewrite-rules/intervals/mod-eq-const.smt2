; rule: mod_eq_const  (_refine_from_eq, reasoner.py:443-452)
; contract: sound narrowing. (mod x p) == c and x canonical in [0,p) => x == c.
; INSTANCE: p=7, x in [0,7), (mod x 7) == 3 => x == 3.
; CHECK: is (x = 3) implied by (0<=x<7 and (mod x 7)=3)?
; EXPECTED: unsat => sound.
(set-logic QF_NIA)
(declare-const x Int)
(assert (<= 0 x))
(assert (< x 7))
(assert (= (mod x 7) 3))
(assert (not (= x 3)))
(check-sat)
