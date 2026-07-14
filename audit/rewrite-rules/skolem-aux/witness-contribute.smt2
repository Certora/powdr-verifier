; rule slug: witness-contribute  (skolem_witness.py::contribute)
; pass: skolem-aux
; contract: unsat-preserving (collapsed free-var witness selection)
;
; RULE
; ----
; Given a collected top-level "collapsed" candidate
;   free_var*(a_0+...+a_k) + c*cmp + const = 0 (mod P),
; for every "expanded" node in the forall body
;   q_0*a_0 + ... + q_k*a_k + c*cmp (+const) = 0 (mod P)
; whose (factor-name-set, cmp-name) matches the candidate, pin each q_i := free_var.
; Materialized as appended disjuncts  q_i != free_var  in the forall body.
;
; WHAT IS BEING CHECKED (soundness)
; ---------------------------------
; Same structural weakening as the other contributors: pins add disjuncts to a
; positive-polarity forall. We check the weakening implication for a 2-qvar body
; with an ARBITRARY free_var witness fv, so soundness holds even when the
; heuristic match (set-based factors, cmp-sign/const ignored) picks a wrong fv.
;
; EXPECTED: unsat (implication valid => sound). A wrong fv only yields a spurious
; sat (incompleteness), never a false PASS.
; See witness-substitution-identity.smt2 for the separate check that the picked
; fv is in fact a valid witness for a WELL-matched pattern (completeness side).

(set-logic UFLIA)
(declare-fun body (Int Int) Bool)
(declare-fun fv () Int)

(assert (forall ((q0 Int) (q1 Int)) (body q0 q1)))
(assert (not (forall ((q0 Int) (q1 Int))
               (or (body q0 q1) (not (= q0 fv)) (not (= q1 fv))))))
(check-sat)
