; rule slug: xor-eq-zero
; pass: bitwise  (_ground_xor_lemmas: x==y case -> term=0, and Iff(x==y, term==0))
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom: uf_xor(x,y) == 0  <=>  x == y
; WHAT IS CHECKED: real xor is 0 iff operands equal.
; EXPECTED: unsat  (unsat = SOUND). sat = byte pair where the biconditional
;   fails for real xor => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun XOR () (_ BitVec 16) (bvxor X Y))
(assert (xor (= XOR #x0000) (= X Y)))
(check-sat)
