; rule slug: probe-exclude-teeth (negative control for probe-exclude)
; pass: domain_probe
; contract: n/a -- this file demonstrates the soundness CHECK has teeth.
;
; PURPOSE
;   probe-exclude.smt2 verifies the real pass by checking  Phi |= rel  where
;   rel is the probe SUBSET.  To show that check would actually FIRE on an
;   unsound variant, we model a HYPOTHETICAL buggy pass that probes over a set
;   that is NOT a subset of Phi: probeset = Phi /\ G with an extra constraint
;   G that is absent from the full script.  Then probeset /\ (x=1) is UNSAT,
;   so the buggy pass would inject (x != 1); but x=1 IS feasible in the true
;   Phi -> that injected fact is NOT implied -> false PASS (unsound).
;
;   The soundness lemma is  Phi |= probeset  <=>  (Phi /\ not probeset) UNSAT.
;   Here it is SAT, correctly flagging the hypothetical variant as unsound.
;
; EXPECTED: sat  => the check correctly REJECTS a non-subset probe set.
;   (The real pass is sound precisely because _cluster_assertions guarantees
;    the probe set is a genuine subset, so this failure mode cannot arise.)
(set-logic QF_NIA)

(declare-fun x () Int)

; True full assertion set: x in {1,2}
(define-fun Phi () Bool (or (= x 1) (= x 2)))
; Extra constraint the buggy probe would (wrongly) include, NOT in Phi:
(define-fun G () Bool (= x 2))
(define-fun probeset () Bool (and Phi G))   ; probeset /\ (x=1) is unsat

; Phi |= probeset ?  ->  (Phi /\ not probeset) should be UNSAT if sound.
(assert Phi)
(assert (not probeset))
(check-sat)
(get-model)
