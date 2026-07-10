; rule slug: xor-zero-ident
; pass: bitwise  (_ground_xor_lemmas: Iff(x==0, term==y) ; Iff(y==0, term==x))
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom: (uf_xor(x,y)==y <=> x==0)  AND  (uf_xor(x,y)==x <=> y==0)
; WHAT IS CHECKED: real xor: x^y==y iff x==0, and x^y==x iff y==0.
; EXPECTED: unsat  (unsat = SOUND). sat = counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun XOR () (_ BitVec 16) (bvxor X Y))
(assert (or
  (xor (= XOR Y) (= X #x0000))
  (xor (= XOR X) (= Y #x0000))))
(check-sat)
