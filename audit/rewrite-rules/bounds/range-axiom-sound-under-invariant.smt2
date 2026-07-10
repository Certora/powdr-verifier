; rule slug: inject-field-range-axiom (soundness under the intended invariant)
; contract: unsat-preserving.
; what is checked: IF the symbol really is a canonical field column (the invariant
;   the pass assumes: every intended model has 0<=x<P), then the injected axiom is a
;   semantic consequence and removes NO intended model, so the transform is sound.
;   We encode the invariant as the hypothesis and check that the injected bound is
;   entailed by it.
; EXPECTED verdict: unsat.
;   unsat = the injected bound is entailed whenever the column is canonical =>
;   adding it deletes no intended model => sound in this regime.  (Confirms the
;   pass is sound exactly when its naming/canonicity invariant holds.)
(set-logic QF_LIA)
(declare-fun x () Int)
; intended invariant for a genuine field column:
(assert (and (<= 0 x) (< x 97)))
; injected axiom, negated:
(assert (not (and (<= 0 x) (< x 97))))
(check-sat)
