; rule: ground-xor  (_ground_xor_lemmas: added AXIOMS about UF_XOR)
; contract: unsat-preserving (axioms must hold in intended model).
; lemmas checked (x!=y branch):
;   L1  Iff(x==y, term==0)          [UNGUARDED -> full range]
;   L2  Iff(x==0, term==y)          [UNGUARDED]
;   L3  Iff(y==0, term==x)          [UNGUARDED]
;   L4  (0<=x<=255 & y==255) -> term==255-x   [byte-guarded]
;   L5  (0<=y<=255 & x==255) -> term==255-y   [byte-guarded]
; width 16 bits: L1-L3 must hold beyond bytes; L4-L5 guarded.
; EXPECTED: unsat = sound. sat = operand values falsifying a lemma.
(set-logic ALL)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(define-fun X () Int (bv2nat x))
(define-fun Y () Int (bv2nat y))
(define-fun T () Int (bv2nat (bvxor x y)))
(define-fun L1 () Bool (= (= X Y) (= T 0)))
(define-fun L2 () Bool (= (= X 0) (= T Y)))
(define-fun L3 () Bool (= (= Y 0) (= T X)))
(define-fun L4 () Bool (=> (and (<= 0 X) (<= X 255) (= Y 255)) (= T (- 255 X))))
(define-fun L5 () Bool (=> (and (<= 0 Y) (<= Y 255) (= X 255)) (= T (- 255 Y))))
(assert (not (and L1 L2 L3 L4 L5)))
(check-sat)
