; rule slug:   skolem-append-disjunct-weakens
; contract:    unsat-preserving
; pass:        skolem-core (SkolemMap.emit_disjuncts / walk_forall)
;
; WHAT IS CHECKED:
;   The literal syntactic step the walker performs, BEFORE lift runs, is
;   "append a disjunct to a positively-occurring forall body". This must not
;   be able to turn a SAT formula UNSAT. We check the implication
;       (forall q. B(q))  =>  (forall q. (B(q) \/ q != w))
;   is valid (negation UNSAT) for an uninterpreted body B and arbitrary w.
;   This is the monotonicity fact that makes the whole pass sound PROVIDED
;   the forall is in positive position (ensured by running nnf first:
;   TACTIC_QEPREFIX = "nnf:skolem:lift:...").
;
; NOTE ON THE PRECONDITION: if nnf were NOT run and a forall sat under a
;   negation (an existential in disguise), appending a disjunct would STRENGTHEN
;   it and could be unsound. The soundness of this pass is conditional on the
;   documented nnf-before-skolem ordering.
;
; EXPECTED: unsat (sound). A 'sat' would mean adding a disjunct to a positive
;   universal removed a model -- impossible; would indicate a polarity bug.

(set-logic UFLIA)
(declare-fun B (Int) Bool)
(declare-fun w () Int)

(assert (forall ((q Int)) (B q)))
(assert (not (forall ((q Int)) (or (B q) (not (= q w))))))

(check-sat)
