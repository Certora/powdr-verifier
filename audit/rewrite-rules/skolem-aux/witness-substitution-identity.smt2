; rule slug: witness-substitution-identity  (skolem_witness.py, completeness side)
; pass: skolem-aux
; contract: equivalence (the substitution q_i := free_var maps expanded -> collapsed)
;
; WHAT IS BEING CHECKED
; ---------------------
; The witness contributor's justification (module docstring): substituting every
; q_i -> free_var turns the EXPANDED lhs
;     q_0*a_0 + q_1*a_1 + c*cmp                (each q_i := fv)
; into the COLLAPSED lhs
;     fv*(a_0 + a_1) + c*cmp .
; This is field distributivity. If it holds mod P, the pinned witness is a
; genuine model witness (rule is not just sound but also complete on matched
; patterns). Checked here for P=7 (see .babybear.smt2 for real P).
;
; NOTE: this identity assumes the expanded and collapsed forms share the SAME
; cmp coefficient sign and constant. The matcher keys only on the factor NAME
; SET and cmp NAME, ignoring cmp-sign and constants; a mismatch there breaks
; this identity and makes fv a WRONG witness -> incompleteness (spurious sat),
; but NOT unsoundness (weakening still holds, see witness-contribute.smt2).
;
; EXPECTED: unsat (distributivity identity is valid mod P).
; A 'sat' model would refute distributivity -- impossible.

(set-logic QF_NIA)
(define-fun P () Int 7)
(declare-fun fv () Int)
(declare-fun a0 () Int)
(declare-fun a1 () Int)
(declare-fun c () Int)
(declare-fun cmp () Int)

(define-fun expanded_sub () Int (+ (* fv a0) (* fv a1) (* c cmp)))
(define-fun collapsed  () Int (+ (* fv (+ a0 a1)) (* c cmp)))

; negation of: (expanded_sub mod P) = (collapsed mod P)
(assert (not (= (mod expanded_sub P) (mod collapsed P))))
(check-sat)
