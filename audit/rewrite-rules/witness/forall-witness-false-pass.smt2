; rule slug: forall-witness-instantiation (soundness / false-PASS demonstration)
; pass: witness  (src/simplify/witness.py :: WitnessSubstituter.walk_forall)
; contract that MUST hold for the verifier: unsat-preserving of the emitted VC
;   (VC UNSAT = equivalence PROVEN = PASS).  A sound transform must never turn a
;   genuinely SAT (counterexample-bearing) VC into UNSAT.
;
; The transform rewrites a matched forall AT ANY DEPTH/POLARITY (IdentityDagWalker,
; no polarity tracking). This file exhibits the NEGATIVE-polarity case, where replacing
; the universal by a single instance STRENGTHENS the assertion and manufactures UNSAT.
;
; Shared context (always asserted): the collapsed top-level witness assert
;     cmp == v*(f0+f1)   (mod 97)
;
; push#1  ORIGINAL VC fragment:  assert (not (forall q. cmp == q*(f0+f1)))
;         EXPECTED: sat  -> a real counterexample exists -> correct verifier verdict = FAIL.
; push#2  TRANSFORMED VC fragment: forall replaced by its single instance Body(v):
;         assert (not (cmp == v*(f0+f1)))
;         EXPECTED: unsat  -> contradicts the collapsed assert -> verifier verdict = PASS.
;
; A sat-then-unsat sequence proves the rewrite converts a SAT (FAIL) VC into an UNSAT
; (PASS) VC: a FALSE PASS = UNSOUND.

(declare-const cmp Int)
(declare-const f0 Int)
(declare-const f1 Int)
(declare-const v Int)

(assert (and (<= 0 cmp) (< cmp 97)
             (<= 0 f0)  (< f0 97)
             (<= 0 f1)  (< f1 97)
             (<= 0 v)   (< v 97)))

; collapsed top-level witness (the assert that seeds `free_var = v`)
(assert (= (mod (- cmp (+ (* v f0) (* v f1))) 97) 0))

(push)
; ORIGINAL: negative-polarity universal
(assert (not (forall ((q Int))
   (=> (and (<= 0 q) (< q 97))
       (= (mod (- cmp (+ (* q f0) (* q f1))) 97) 0)))))
(check-sat)   ; expect sat  (original VC = FAIL, has counterexample)
(pop)

(push)
; TRANSFORMED: universal replaced by its single instance Body(v)
(assert (not (= (mod (- cmp (+ (* v f0) (* v f1))) 97) 0)))
(check-sat)   ; expect unsat (transformed VC = false PASS)
(pop)
