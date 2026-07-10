; rule: ground-or  (_ground_or_lemmas: added AXIOMS about UF_OR)
; contract: unsat-preserving.
; lemmas (x!=y branch):
;   L1  x==y -> term==x            [unguarded]
;   L2  x==0 -> term==y            [unguarded]
;   L3  y==0 -> term==x            [unguarded]
;   L4  (0<=x<=255 & y==255) -> term==255   [guarded]
;   L5  (0<=y<=255 & x==255) -> term==255   [guarded]
; EXPECTED: unsat = sound.
(set-logic ALL)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(define-fun X () Int (bv2nat x))
(define-fun Y () Int (bv2nat y))
(define-fun T () Int (bv2nat (bvor x y)))
(define-fun L1 () Bool (=> (= X Y) (= T X)))
(define-fun L2 () Bool (=> (= X 0) (= T Y)))
(define-fun L3 () Bool (=> (= Y 0) (= T X)))
(define-fun L4 () Bool (=> (and (<= 0 X) (<= X 255) (= Y 255)) (= T 255)))
(define-fun L5 () Bool (=> (and (<= 0 Y) (<= Y 255) (= X 255)) (= T 255)))
(assert (not (and L1 L2 L3 L4 L5)))
(check-sat)
