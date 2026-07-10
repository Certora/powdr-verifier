; rule: fold-xor  (walk_function constant folding of UF_XOR)
; contract: equivalence  (UF_XOR(x,0)->x, UF_XOR(0,y)->y, UF_XOR(x,x)->0)
; check: genuine bitwise xor satisfies x^0=x, 0^y=y, x^x=0 for ALL nonneg ints
;        (folds are UNGUARDED in code -> must hold on full range, not just bytes).
; width 16 bits => tests non-byte operands too.
; EXPECTED: unsat = sound. sat model = a value where a fold replaces a term with
;           the wrong value (would corrupt the VC).
(set-logic ALL)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(define-fun X () Int (bv2nat x))
(define-fun Y () Int (bv2nat y))
(define-fun Xxor0 () Int (bv2nat (bvxor x #x0000)))
(define-fun zeroXORy () Int (bv2nat (bvxor #x0000 y)))
(define-fun XxorX () Int (bv2nat (bvxor x x)))
(assert (or (not (= Xxor0 X)) (not (= zeroXORy Y)) (not (= XxorX 0))))
(check-sat)
