; rule slug: guard-acyclic (GUARD-NECESSITY test, not the shipped rule)
; pass: solve_eqs
; contract: equisat. Demonstrates WHY the code's acyclicity guard
;   (x not in free-vars(e), line ~86) is load-bearing.
;   The shipped code REFUSES to eliminate (= x e) when x occurs in e.
;
; SETUP:
;   Original:  (= x (+ x 1))   over Int  -- UNSAT (no integer equals its succ).
;   If a tool ignored acyclicity and did x := x+1 then dropped the equality,
;   the assertion becomes (and) = True -- SAT. That is UNSAT -> SAT flip:
;   it turns a real counterexample-free (proven) obligation into ... actually
;   here it converts an UNSAT assumption into SAT, i.e. LOSES the contradiction.
;   For a VC checked-for-unsat, silently making an unsat assumption-set sat is
;   unsound (the substitution x:=x+1 is not a well-defined witness).
;
; EXPECTED VERDICT: FIRST check-sat = unsat (original is contradictory),
;                   SECOND check-sat = sat (naive cyclic substitution erased it).
;   The unsat/sat split proves the acyclic guard is required. The shipped rule
;   AVOIDS this because eligible() returns False when sym in fvo free-vars(expr).

(set-logic QF_LIA)
(declare-const x Int)

; --- original: contradictory equality ---
(push 1)
(assert (= x (+ x 1)))
(check-sat)          ; expect: unsat
(pop 1)

; --- result of ILLEGAL cyclic elimination x := x+1, equality dropped ---
(push 1)
(assert true)
(check-sat)          ; expect: sat  (SOUNDNESS BUG if a tool did this)
(pop 1)
