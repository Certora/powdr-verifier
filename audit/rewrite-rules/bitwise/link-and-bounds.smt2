; rule slug: link-and-bounds
; pass: bitwise  (_ground_linking_lemmas conjunct 2)
; contract: unsat-preserving (adds axiom). Sound iff true for real bytes.
; axiom (byte-guarded): 0 <= uf_and(x,y) <= x  AND  uf_and(x,y) <= y
; WHAT IS CHECKED: real AND of two bytes is nonneg and <= each operand.
; EXPECTED: unsat  (unsat = SOUND). sat = a byte pair with real (x&y) > x or > y
;   => axiom false => could kill a real counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun AND () (_ BitVec 16) (bvand X Y))
; unsigned comparisons; 0 <= AND is automatic for unsigned
(assert (or (bvugt AND X) (bvugt AND Y)))
(check-sat)
