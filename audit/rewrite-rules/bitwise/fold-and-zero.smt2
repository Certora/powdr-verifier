; rule slug: fold-and-zero
; pass: bitwise  (walk_function constant-fold for UF_AND)
; contract: equivalence (term rewrite)
; rewrite: UF_AND(x,0)->0 ; UF_AND(0,y)->0 ; UF_AND(x,x)->x
; WHAT IS CHECKED: byte-wise AND (bvand) satisfies x&0=0, 0&y=0, x&x=x.
; EXPECTED: unsat  (unsat = SOUND). sat = a byte where real AND disagrees => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(assert (or
  (not (= (bvand X #x0000) #x0000))
  (not (= (bvand #x0000 Y) #x0000))
  (not (= (bvand X X) X))))
(check-sat)
