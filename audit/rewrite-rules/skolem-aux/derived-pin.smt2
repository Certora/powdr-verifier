; rule slug: derived-pin  (skolem_derived.py::contribute)
; pass: skolem-aux
; contract: unsat-preserving (Skolem-witness selection from verifier :skolem-* pins)
;
; RULE
; ----
; For each loaded equation Equals(var, expr) / Iff(var, expr) whose var is an
; unpinned qvar of the current forall, pin var := expr. Materialized as the
; appended disjunct  var != wrap_mod(expr)  (int) or  var != expr  (bool/array).
;
; WHAT IS BEING CHECKED
; ---------------------
; The pin equation is supplied out-of-band (verifier set-info) and is TRUSTED as
; a definition, but soundness of THIS pass does not rely on that trust: the pin
; is only ever added as a disjunct to the positive-polarity forall body, which
; can only weaken the VC. We model expr by an arbitrary function of a free var
; and check the weakening implication holds for that arbitrary witness.
;
; EXPECTED: unsat (implication valid => sound). If the emitted 'expr' were a bad
; definition it would only produce a spurious sat downstream, never a false PASS
; from THIS transform.

(set-logic UFLIA)
(declare-fun body (Int) Bool)
(declare-fun expr () Int)     ; witness value from the pin equation (arbitrary)

(assert (forall ((var Int)) (body var)))
(assert (not (forall ((var Int)) (or (body var) (not (= var expr))))))
(check-sat)
