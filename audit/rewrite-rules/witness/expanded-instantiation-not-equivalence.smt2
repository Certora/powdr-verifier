; rule slug: expanded-witness-universal-instantiation (strictness / completeness note)
; contract: other (documents that the rewrite is a STRICT weakening, not an equivalence).
; pass: witness (src/simplify/witness.py)
;
; WHAT THIS CHECKS: the reverse implication does NOT hold:
;   P(fv)  =/=>  (forall q. P(q)).
; We assert the instance P(fv) together with the negation of the universal and
; look for a model. A model shows the ground instance is strictly weaker than
; the universal it replaces.
;
; EXPECTED VERDICT: sat  (=> instance is strictly weaker than the universal).
;   Consequence: the pass can turn a genuinely-UNSAT (proven-equivalent, PASS)
;   VC into SAT (spurious counterexample) => a false FAIL. That is an
;   INCOMPLETENESS, not an unsoundness -- acceptable for the verifier.
;   (Combined with expanded-instantiation-soundness.smt2 this pins the rewrite
;   as sound-but-lossy: implication one way only.)
;
; A trivial model: f0=1 f1=0 cmp=0 fv=0 makes P(fv) hold (0=0) while q0=1
; violates the universal (1 mod 7 != 0).
(set-logic UFNIA)
(declare-fun f0 () Int)
(declare-fun f1 () Int)
(declare-fun cmp () Int)
(declare-fun fv () Int)
; instance P(fv,fv) holds
(assert (= (mod (- (+ (* fv f0) (* fv f1)) cmp) 7) 0))
; but the universal fails
(assert (not (forall ((q0 Int) (q1 Int))
               (= (mod (- (+ (* q0 f0) (* q1 f1)) cmp) 7) 0))))
(check-sat)
(get-value (f0 f1 cmp fv))
