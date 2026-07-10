; rule slug: inject-field-range-axiom (redundancy probe)
; contract: unsat-preserving (this pass ADDS a hypothesis 0<=x<P for symbols
;   named "...@<digits>" to a VC that is checked for UNSAT).
; what is checked: is the injected bound REDUNDANT given only that x is an
;   ordinary Int field-encoding symbol (no prior range constraint)?  If it is
;   NOT redundant, the pass genuinely narrows the model space, which is the
;   direction that can turn a SAT (counterexample-bearing => NOT proven) VC into
;   UNSAT (false PASS).  Redundancy would make the pass trivially sound.
; EXPECTED verdict: sat.
;   sat model = a value of x (e.g. -1 or P) that satisfies "x is a field Int"
;   but violates the injected bound => the axiom carries real information and its
;   soundness rests entirely on the external invariant that "@<digits>" symbols
;   are truly canonical field columns in [0,P).  (sat here = NOT sound-by-triviality.)
(set-logic QF_LIA)
(declare-fun x () Int)
; "x is used as a field element via mod-equality" imposes no range on x itself:
(assert (= (mod x 97) 3))
; is the injected bound entailed?  negate it:
(assert (not (and (<= 0 x) (< x 97))))
(check-sat)
(get-value (x))
