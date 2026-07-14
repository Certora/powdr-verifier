; rule slug : def_fold  (BabyBear real-prime variant of def_fold.smt2)
; contract  : unsat-preserving
; what      : same check as def_fold.smt2 but with the real field prime.
; expected  : unsat => SOUND.  MAY TIME OUT (QF_NIA with a ~2^31 modulus).
(set-logic QF_NIA)
(define-fun P () Int 2013265921)   ; 0x78000001, BabyBear prime
(declare-fun T () Int)
(declare-fun C () Int)
(declare-fun V () Int)
(declare-fun I () Int)

(assert (and (<= 0 T) (< T P)))
(assert (and (<= 0 C) (< C P)))
(assert (and (<= 0 V) (< V P)))
(assert (and (<= 0 I) (< I P)))

(assert (=> (not (= (mod T P) 0)) (= (mod (* I T) P) 1)))
(assert (=> (= (mod T P) 0) (= V 0)))
(assert (=> (not (= (mod T P) 0)) (= V (mod (* C I) P))))

(assert (not (and
   (=> (= (mod T P) 0)       (= V 0))
   (=> (not (= (mod T P) 0)) (= (mod (* T V) P) (mod C P))))))

(check-sat)
