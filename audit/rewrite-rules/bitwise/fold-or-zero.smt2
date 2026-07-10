; rule slug: fold-or-zero
; pass: bitwise  (walk_function constant-fold for UF_OR)
; contract: equivalence (term rewrite)
; rewrite: UF_OR(0,y)->y ; UF_OR(x,0)->x ; UF_OR(x,x)->x
; WHAT IS CHECKED: byte-wise OR (bvor) satisfies 0|y=y, x|0=x, x|x=x.
; EXPECTED: unsat  (unsat = SOUND). sat = counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(assert (or
  (not (= (bvor #x0000 Y) Y))
  (not (= (bvor X #x0000) X))
  (not (= (bvor X X) X))))
(check-sat)
