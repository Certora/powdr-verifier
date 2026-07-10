; rule slug: pin-eq-lift-multivar
; pass: lift_forall
; contract: equivalence
;
; WHAT: multi-variable forall where ONE var is pinned and the quantifier
;   prefix is shrunk to the remaining vars (the code path that returns
;   ForAll(qvars_remaining, body_out) instead of the bare body).
;     forall q,o. ( (q != e) | R(q,o) )
;   becomes:  (exists q. q = e & (forall o. R(q,o)))
;   i.e. top-level pin q=e plus  forall o. R(q,o)  with q now free.
;
; CHECK: assert SRC and DST differ -> expect UNSAT (sound equivalence).
; EXPECTED VERDICT: unsat => sound.
;   'sat' would mean shrinking the prefix while pinning q changed meaning.

(set-logic UFLIA)
(declare-fun e () Int)
(declare-fun R (Int Int) Bool)

(define-fun SRC () Bool
  (forall ((q Int) (o Int)) (or (not (= q e)) (R q o))))

; peel result: pin q=e, remaining quantifier over o, q free inside.
(define-fun DST () Bool
  (exists ((q Int)) (and (= q e) (forall ((o Int)) (R q o)))))

(assert (not (= SRC DST)))
(check-sat)
