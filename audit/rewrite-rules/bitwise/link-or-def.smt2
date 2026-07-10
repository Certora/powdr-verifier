; rule slug: link-or-def
; pass: bitwise  (_ground_linking_lemmas conjunct 3)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom (byte-guarded): uf_or(x,y) = x + y - uf_and(x,y)  AND  0 <= uf_or <= 255
; WHAT IS CHECKED: real OR equals x+y-(x&y) and is a byte, for byte inputs.
; EXPECTED: unsat  (unsat = SOUND). sat = byte pair where real OR != x+y-(x&y)
;   or real OR > 255 => axiom false => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun AND () (_ BitVec 16) (bvand X Y))
(define-fun OR  () (_ BitVec 16) (bvor  X Y))
(assert (or
  (not (= OR (bvsub (bvadd X Y) AND)))
  (bvugt OR #x00FF)))
(check-sat)
