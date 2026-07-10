; rule slug: eqmod-zero-solve  (variant: WITH the missing range precondition)
; source: _demod_rewrite_eqmod_zero_equals (demod.py:92-111)
; contract: equivalence, but ONLY under the precondition 0 <= x < p (field_symbol axiom)
; What is checked: if x is known to be a field element (0<=x<97), is
;   (mod (x+3) 97)=0  <=>  x=94 ?   With the range axiom present this SHOULD hold.
; EXPECTED: unsat  => confirms the rewrite is sound EXACTLY WHEN the field-range
;   axiom for x is present in the VC.  Since demod.py applies the rewrite without
;   checking for / requiring this axiom, the rewrite is unsound for any x that
;   lacks it (see eqmod-zero-solve.smt2).  A 'sat' here would mean even the
;   range-guarded rewrite is wrong.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (and (<= 0 x) (< x 97)))          ; field_symbol range axiom
; equivalence check: A xor B must be unsatisfiable
(assert (not (= (= (mod (+ x 3) 97) 0) (= x 94))))
(check-sat)
