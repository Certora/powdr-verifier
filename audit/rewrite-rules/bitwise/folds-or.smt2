; rule: fold-or  (walk_function constant folding of UF_OR)
; contract: equivalence  (UF_OR(0,y)->y, UF_OR(x,0)->x, UF_OR(x,x)->x)
; check: 0|y=y, x|0=x, x|x=x for ALL nonneg ints (folds unguarded).
; EXPECTED: unsat = sound.
(set-logic ALL)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(define-fun X () Int (bv2nat x))
(define-fun Y () Int (bv2nat y))
(define-fun zeroORy () Int (bv2nat (bvor #x0000 y)))
(define-fun Xor0 () Int (bv2nat (bvor x #x0000)))
(define-fun XorX () Int (bv2nat (bvor x x)))
(assert (or (not (= zeroORy Y)) (not (= Xor0 X)) (not (= XorX X))))
(check-sat)
