; rule slug: or-eq-zero
; pass: bitwise  (_ground_or_lemmas: x==y->term==x ; x==0->term==y ; y==0->term==x)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; WHAT IS CHECKED: real OR: x|x==x ; 0|y==y ; x|0==x.
; EXPECTED: unsat  (unsat = SOUND). sat = counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun OR () (_ BitVec 16) (bvor X Y))
(assert (or
  (and (= X Y) (not (= OR X)))
  (and (= X #x0000) (not (= OR Y)))
  (and (= Y #x0000) (not (= OR X)))))
(check-sat)
