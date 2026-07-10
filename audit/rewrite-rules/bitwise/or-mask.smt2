; rule slug: or-mask
; pass: bitwise  (_ground_or_lemmas: byte(x) & y==255 -> term==255 ; symmetric)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom: (0<=x<=255 AND y==255) -> uf_or(x,y) == 255
; WHAT IS CHECKED: OR of a byte with all-ones is all-ones. Needs byte guard on
;   the other operand (x <= 255) so no higher bits push the result above 255.
; EXPECTED: unsat  (unsat = SOUND). sat = byte x with x|255 != 255 => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(assert (not (= (bvor X #x00FF) #x00FF)))
(check-sat)
