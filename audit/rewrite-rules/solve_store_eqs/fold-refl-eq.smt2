; rule slug: fold-refl-eq
; pass: solve_store_eqs  (_FoldRefl walker: walk_equals, walk_and/or/not)
; contract: equivalence  (local Boolean/reflexivity simplification)
;
; RULE(s) applied after substitution to collapse the definitional equality:
;   (= e e)            -> True        [reflexivity, any type incl. arrays/stores]
;   (and ... True ...) -> (and ...)   [drop True conjuncts]
;   (or  ... False ..) -> (or  ...)   [drop False disjuncts]
;   (not True)->False, (not False)->True
;
; After arr:=E substitution, (= arr E) becomes (= E E) -> True; and a negated
; (not (= arr E)) becomes (not (= E E)) -> (not True) -> False, which drops the
; disjunct. This validator checks the reflexivity fold is sound even when e is a
; nested store term (the collapse relies only on structural identity of e).
;
; WHAT IS CHECKED: (= e e) with e a 2D store term must be True; and the derived
; (not (= e e)) must be False.
;     goal: NOT ( (= e e) AND (not (not (= e e))) )   -> expect UNSAT
;
; EXPECTED VERDICT: unsat => SOUND. 'sat' would mean e != e for some model.

(set-logic ALL)

(declare-fun base  () (Array Int (Array Int Int)))
(declare-fun inner () (Array Int Int))
(declare-fun i0 () Int)

(define-fun e () (Array Int (Array Int Int)) (store base i0 inner))

; e = e must be True; check its negation is unsatisfiable.
(assert (not (= e e)))

(check-sat)
