; rule: modular_ineq_decline  (normalize.normalize_int_rel_gcd: modular => return None)
; contract: unsat-preserving (the transform must not manufacture UNSAT)
; This validates WHY the current code DECLINES to rewrite modular inequalities.
; The OLD buggy transform was:  (< a b)  ->  (< (mod (a-b) P) 0).
; Since Euclidean (mod _ P) is always in [0,P), (< (mod (a-b) P) 0) is
; UNCONDITIONALLY FALSE -- so a satisfiable assumption (a<b) got rewritten into
; an unsatisfiable one, manufacturing a false PASS (UNSOUND).
; check: assert the old rewrite is NOT equivalent to the original for some a,b.
; EXPECTED: sat  (=> the OLD rule was UNSOUND; hence the fix's decline is REQUIRED
;   and CORRECT). A model has a<b (original true) while (mod (a-b) P) < 0 is false.
; The CURRENT code produces no such rewrite (it keeps the original untouched),
; so the current pass is sound on this construct.
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(define-fun P () Int 97)
(assert (not (= (< a b)
                (< (mod (- a b) P) 0))))
(check-sat)
