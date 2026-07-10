; rule slug: inject-field-range-axiom (false-PASS witness)
; contract: unsat-preserving.  The verifier checks VCs for UNSAT; UNSAT = PROVEN = PASS.
; what is checked: exhibit a satisfiable assumption set (counterexample exists =>
;   the equivalence step is NOT proven) that becomes UNSAT after the bounds pass
;   injects 0<=x<P.  This is the concrete unsound direction (SAT -> UNSAT = false PASS),
;   realised whenever a symbol matching the "@<digits>" regex is NOT actually a
;   canonical field column (e.g. a mis-named non-field helper, a timestamp, or a
;   non-canonicalised representative that legitimately equals 100 in some model).
; EXPECTED verdict: first (check-sat) = sat ; second (check-sat) = unsat.
;   The sat->unsat flip demonstrates the pass can manufacture a false PASS when the
;   naming invariant it relies on does not hold.  Soundness is thus CONDITIONAL on
;   that invariant, which is not enforced in bounds.py.
(set-logic QF_LIA)
(declare-fun x () Int)          ; stands in for a symbol named e.g. cnt@0
(push 1)
  ; original VC assumptions: field-equality holds AND the raw column value is 100
  (assert (= (mod x 97) 3))     ; 100 mod 97 = 3, consistent
  (assert (= x 100))            ; a legitimate non-canonical / non-field value
  (check-sat)                   ; expect: sat  (counterexample-bearing, NOT proven)
(pop 1)
(push 1)
  (assert (= (mod x 97) 3))
  (assert (= x 100))
  ; bounds pass injects the field-range axiom:
  (assert (and (<= 0 x) (< x 97)))
  (check-sat)                   ; expect: unsat (false PASS: proven that was not)
(pop 1)
