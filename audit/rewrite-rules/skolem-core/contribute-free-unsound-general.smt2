; rule slug: skolem-rules-contribute_free  (GENERAL / no-precondition control)
; contract: unsat-preserving
; pass: skolem-core (src/simplify/skolem_rules.py:contribute_free + skolem.py:155-166)
;
; WHAT THE RULE DOES:
;   Unlike every other skolem contributor (which pin QUANTIFIED vars by appending
;   Not(q=w) disjuncts -- a pure weakening), contribute_free inserts a TOP-LEVEL
;       (assert (= v e))
;   for a FREE (non-quantified) declared variable v (an OpenVM after-side
;   diff_val/diff_marker whose defining constraints were dropped by the powdr
;   rule_based optimizer), with e the canonical OpenVM witness in after-side vars.
;
; WHY THIS IS THE SOUNDNESS FULCRUM:
;   A free top-level var is existentially closed for SAT. Adding (v = e) is a
;   STRENGTHENING, not a weakening. It is unsat-preserving (no false PASS) ONLY IF
;       (exists v. Phi(v))  ==>  Phi(e)
;   i.e. e is a UNIFORM witness: either v is genuinely unconstrained by the rest
;   of the assumptions Phi, or Phi implies v=e. The code ASSUMES v is unconstrained
;   ("lost its defining constraints ... but remains referenced in bus interactions")
;   but does NOT verify that no remaining assertion forces v to a different value.
;
; WHAT IS CHECKED (counterexample to UNCONDITIONAL soundness):
;   Model a case where Phi DOES constrain v (Phi(v): v = d, a residual bus/other
;   assertion) and the pinned e differs from d. Then (exists v. v=d) holds but
;   Phi(e) = (e=d) fails. Negated soundness lemma:
;       (exists v. Phi(v)) /\ not Phi(e).
; Domain: field [0,7).
; EXPECTED: sat.  A 'sat' model (e.g. d=0, e=1) is a witness that adding (v=e) for
;   a CONSTRAINED free var turns a SAT assumption set UNSAT -> a false PASS. This
;   proves contribute_free is UNSOUND in general and sound only under the
;   unverified "v is a uniform/unconstrained witness" invariant.
(set-logic UFLIA)
(declare-fun d () Int)
(declare-fun e () Int)
(assert (and (<= 0 d) (< d 7) (<= 0 e) (< e 7)))
; (exists v. v = d) is trivially true; encode the residual: some model has v=d.
; not Phi(e): e != d  (the pinned value conflicts with the value v is forced to)
(assert (not (= e d)))
(check-sat)
