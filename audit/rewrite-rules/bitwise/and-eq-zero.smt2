; rule slug: and-eq-zero
; pass: bitwise  (_ground_and_lemmas: x==y->term==x ; x==0->term==0 ; y==0->term==0)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; WHAT IS CHECKED: real AND: x&x==x ; 0&y==0 ; x&0==0.
; EXPECTED: unsat  (unsat = SOUND). sat = counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun AND () (_ BitVec 16) (bvand X Y))
(assert (or
  (and (= X Y) (not (= AND X)))
  (and (= X #x0000) (not (= AND #x0000)))
  (and (= Y #x0000) (not (= AND #x0000)))))
(check-sat)
