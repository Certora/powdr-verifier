; rule slug : fallback_axiom  (COMPOSITE-modulus sensitivity check)
; contract  : demonstrates the prime-dependence of fallback_axiom soundness.
; what      : identical to fallback_axiom.smt2 but with a COMPOSITE modulus.
;             Nonzero non-units (e.g. 2,3,4 mod 6) have no multiplicative inverse.
; expected  : sat  => there IS a nonzero T with no inverse; for such T the fallback
;                     constraint  (T!=0 => I*T=1)  is unsatisfiable, so the rewrite
;                     would turn a SAT original into UNSAT (UNSOUND) if P were composite.
;             This is NOT a bug for BabyBear (P is prime); it only pins WHY the rule
;             needs primality.  A 'sat' model here is the expected/correct outcome.
(set-logic NIA)
(define-fun P () Int 6)             ; COMPOSITE
(declare-fun T () Int)
(assert (and (<= 1 T) (< T P)))
(assert (forall ((I Int))
   (=> (and (<= 0 I) (< I P))
       (not (= (mod (* I T) P) 1)))))
(check-sat)
