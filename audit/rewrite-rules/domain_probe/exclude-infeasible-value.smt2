; rule slug:   exclude-infeasible-value
; pass:        domain_probe
; contract:    unsat-preserving / equisat (learn an implied unit fact)
;
; WHAT THE PASS DOES:
;   For a "choice" variable sym constrained by (or (= sym c1) (= sym c2) ...),
;   it probes each candidate value v by asking a solver whether
;       rel  /\  (= sym v)
;   is UNSAT, where `rel` is the CLUSTER-LOCAL SUBSET of assertions
;   (rel = { a in assertions : freevars(a) subset of cluster }).
;   If UNSAT, it injects  (not (= sym v))  as a new assertion into the script.
;
; SOUNDNESS ARGUMENT (this file corroborates it):
;   rel is a SUBSET of the full assertion set F (a filter, never a superset).
;   Models(F) subset Models(rel).  If rel /\ (sym=v) is UNSAT then
;   F /\ (sym=v) is UNSAT (a superset of constraints can only lose models).
;   Hence F |= (sym != v): the injected fact is ENTAILED by the full VC body,
;   so adding it preserves every model of F  ==>  SAT stays SAT, UNSAT stays
;   UNSAT. No false PASS can be manufactured.
;
; WHAT THIS FILE CHECKS (the direction that matters for soundness):
;   Concrete P=97 instance where the SUBSET rel forces sym=10 (via a modular
;   equation), so probing sym=5 yields rel/\(sym=5) UNSAT and the pass injects
;   (sym != 5). We then ask whether the FULL set F (rel plus an UNRELATED extra
;   constraint on another var) admits a model with sym=5 -- i.e. whether the
;   injected fact could be false in some model of F.
;
; EXPECTED: unsat  (= sound: no model of F violates the injected fact).
; A 'sat' model would mean F allows sym=5 even though the subset excluded it,
;   i.e. the pass excluded a live counterexample value == UNSOUND.

(set-logic QF_NIA)
(define-fun P () Int 97)

(declare-fun x () Int)   ; the choice variable
(declare-fun y () Int)   ; an unrelated variable (only in the "extra" constraint)

; ---- rel : the cluster-local SUBSET the pass actually probes against ----
; choice constraint: x in {5, 10, 20}
(assert (or (= x 5) (= x 10) (= x 20)))
; a modular equation in rel that pins x == 10 (mod P): x - 10 == 0 (mod P)
(assert (= (mod (- x 10) P) 0))

; ---- extra : belongs to full F but NOT to rel (mentions y, outside cluster) ----
(assert (= (mod (- y 3) P) 0))

; ---- negation of the injected fact: try to realize the excluded value ----
(assert (= x 5))

(check-sat)
