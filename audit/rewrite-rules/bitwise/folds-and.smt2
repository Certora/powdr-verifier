; rule: fold-and  (walk_function constant folding of UF_AND)
; contract: equivalence  (UF_AND(x,0)->0, UF_AND(0,y)->0, UF_AND(x,x)->x)
; check: x&0=0, 0&y=0, x&x=x for ALL nonneg ints (folds unguarded).
; EXPECTED: unsat = sound.
(set-logic ALL)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(define-fun X () Int (bv2nat x))
(define-fun Xand0 () Int (bv2nat (bvand x #x0000)))
(define-fun zeroANDy () Int (bv2nat (bvand #x0000 y)))
(define-fun XandX () Int (bv2nat (bvand x x)))
(assert (or (not (= Xand0 0)) (not (= zeroANDy 0)) (not (= XandX X))))
(check-sat)
