; rule slug: guard-conjunctive (GUARD-NECESSITY test, not the shipped rule)
; pass: solve_eqs
; contract: equisat. This file demonstrates WHY the code's conjunctive-context
;   guard (descend only through And; stop at or/not/ite/=>) is load-bearing.
;   It encodes the UNGUARDED transform: eliminating an equality (= x 5) that
;   sits under a DISJUNCTION. The shipped code REFUSES this (correctly).
;
; SETUP (P=97 field flavor via mod, but the point is structural):
;   Original body:  (or (= x 5) (= x 7)) /\ (> x 6)      -- SAT, witness x=7.
;   If a tool wrongly treated (= x 5) as eliminable and did x:=5 + dropped it:
;     (or true (= 5 7)) /\ (> 5 6)  =  (> 5 6)  = FALSE  -- UNSAT.
;   That is a SAT -> UNSAT flip: it manufactures a false PASS. UNSOUND.
;
; EXPECTED VERDICT: FIRST check-sat = sat (original has a model),
;                   SECOND check-sat = unsat (unguarded substitution kills it).
;   The sat/unsat split is the counterexample proving the guard is required.
;   The shipped rule AVOIDS this because (= x 5) is not reachable through
;   only-And nodes, so _find_candidate_in_conjunct never returns it.

(set-logic QF_LIA)
(declare-const x Int)

; --- original formula (what the verifier actually has) ---
(push 1)
(assert (and (or (= x 5) (= x 7)) (> x 6)))
(check-sat)          ; expect: sat  (x = 7)
(pop 1)

; --- result of UNGUARDED elimination of the disjunct (= x 5): x := 5 ---
(push 1)
(assert (and (or true (= 5 7)) (> 5 6)))
(check-sat)          ; expect: unsat  (SOUNDNESS BUG if a tool did this)
(pop 1)
