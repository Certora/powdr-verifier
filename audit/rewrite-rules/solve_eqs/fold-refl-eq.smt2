; rule slug: fold-refl-eq
; pass: solve_eqs  (_FoldRefl.walk_equals)
; contract: EQUIVALENCE  ( (= e e) -> True )
;
; RULE: after substitution, any (= e e) is folded to True. Sound iff (= e e) is a
;   tautology for every well-formed term e. In this domain all functions (mod,+,*,
;   array select/store, const-array) are total, so reflexivity holds unconditionally.
;
; Check: is there a model where (= e e) is false? Use a representative field term.
; EXPECTED: unsat => (= e e) always True => rule SOUND.
;   'sat' would be a term e for which e != e (impossible for total functions).
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(define-fun P () Int 97)
(define-fun e () Int (mod (+ (* a b) a) P))
(assert (not (= e e)))
(check-sat)
