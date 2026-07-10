; rule: mod_ineq_is_tautology  (_mod_ineq_is_tautology, reasoner.py:351-371)
; contract: recognizes tautologies on (mod e p) to SKIP refinement (skipping is always safe).
;   Here we validate the recognized facts are genuine tautologies (Euclidean mod in [0,p-1]).
; INSTANCE: p=7. Checks: 0 <= (mod e 7);  (mod e 7) <= 6;  (mod e 7) < 7;  -1 < (mod e 7).
; CHECK: negation of the conjunction of all four claimed tautologies.
; EXPECTED: unsat => sound (all four hold for every e).
(set-logic QF_NIA)
(declare-const e Int)
(assert (not (and
  (<= 0 (mod e 7))
  (<= (mod e 7) 6)
  (< (mod e 7) 7)
  (< (- 1) (mod e 7)))))
(check-sat)
