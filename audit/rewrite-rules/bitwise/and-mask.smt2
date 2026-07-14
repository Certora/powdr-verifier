; rule slug: and-mask
; pass: bitwise  (_ground_and_lemmas: byte(x) & y==255 -> term==x ; symmetric)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom: (0<=x<=255 AND y==255) -> uf_and(x,y) == x
; WHAT IS CHECKED: masking a byte with all-ones is identity. Needs byte guard
;   (would fail if x had bits above bit 7).
; EXPECTED: unsat  (unsat = SOUND). sat = byte x with x&255 != x => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(assert (not (= (bvand X #x00FF) X)))
(check-sat)
