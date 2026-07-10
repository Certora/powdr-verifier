; rule slug: inject-field-range  (FAILURE-MODE probe)
; pass: bounds  (src/simplify/bounds.py)
; CONTRACT: unsat-preserving. This file probes the ONE way the rule can be unsound:
;   the naming heuristic _BOUNDED_INT_VAR_RE = /@[0-9]+$/ misclassifies an Int
;   symbol that is NOT a canonical field element (e.g. a raw/non-reduced integer, a
;   value the encoder legitimately allows to reach or exceed P) as a bounded column.
;   If such a symbol can legitimately take a value outside [0,P), then injecting
;   0<=x<P DISCARDS a real distinguishing model: SAT(original) becomes UNSAT =>
;   false PASS => UNSOUND.
;
; WHAT THIS FILE CHECKS: construct an "original" assumption set S that is SAT only
;   with x = P (=97), representing a legitimate model in which the mis-tagged symbol
;   sits at the non-canonical value P. Then conjoin the injected axiom. If the
;   combination is UNSAT, the axiom eliminated that model -- demonstrating the
;   SAT->UNSAT flip that would be unsound IF x=P were a genuine input.
;   Uses P = 97.
;
; EXPECTED: unsat  (= the injected axiom kills the x=P model).
;   Interpretation: unsat here does NOT by itself prove the pass is buggy; it proves
;   the transform is only sound under the modeling assumption that every @<digits>
;   Int is a canonical field element in [0,P). The pass's soundness rests entirely
;   on that encoder invariant, which this repro isolates.
(set-logic QF_NIA)
(declare-fun x () Int)
(define-fun P () Int 97)
; original S: a legitimate (per the probe) model at the non-canonical value P
(assert (= x P))
; injected axiom
(assert (and (<= 0 x) (< x P)))
(check-sat)
