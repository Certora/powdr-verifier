; rule slug: eq_mod_zero_open_pm
; pass: intervals   file: src/simplify/intervals/reasoner.py  simplify() equals branch (lines 1044-1061)
; contract: equivalence, under guard  x in (-P, P)  (within_open_pm_p).
;   Rewrites  (= (mod x P) 0)  ->  (= x 0)  when x's domain is within (-P,P),
;   since 0 is the only multiple of P in (-P,P).
;
; CHECK (P=7): under -7 < x < 7, are  ((mod x 7)=0)  and  (x=0)  equivalent?
;   Assert -7<x<7 AND the two atoms differ.
; EXPECTED: unsat  => equivalent under the guard => SOUND.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (< (- 7) x))
(assert (< x 7))
(assert (distinct (= (mod x 7) 0) (= x 0)))
(check-sat)
