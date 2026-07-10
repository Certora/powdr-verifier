; rule slug: xor-comp
; pass: bitwise  (_ground_xor_lemmas: byte(x) & y==255 -> term==255-x ; symmetric)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom: (0<=x<=255 AND y==255) -> uf_xor(x,y) == 255-x   (and x<->y symmetric)
; WHAT IS CHECKED: xor with all-ones byte is the bit-complement 255-x. This is
;   THE lemma that genuinely needs the byte guard (fails if x has bits above bit7).
; EXPECTED: unsat  (unsat = SOUND). sat = byte x with x^255 != 255-x => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun ALLONES () (_ BitVec 16) #x00FF)
; y == 255 branch: xor(x,255) must be 255 - x
(assert (not (= (bvxor X ALLONES) (bvsub #x00FF X))))
(check-sat)
