; rule slug: derived-pin-instantiation  (skolem_derived.contribute)
; contract: unsat-preserving (weakening of a positively-occurring forall)
;
; WHAT THE RULE DOES
;   For a positive forall over qvar `q`, and a verifier-emitted pin equation
;   Equals(q, expr) (expr an arbitrary term over free vars), pins q := expr.
;   emit_disjuncts rewrites  (forall ((q Int)) body(q))  to
;       (forall ((q Int)) (or body(q) (not (= q (mod expr P))))).
;   Here `expr` is modeled as an arbitrary uninterpreted term `expr` over a
;   free var a. The witness being "correct" is irrelevant to soundness:
;   appending ANY disjunct to a positive forall body only weakens it.
;
; WHAT IS CHECKED:  original ==> rewritten (weakening) is VALID.
;   assert (and ORIG (not WEAK)).
; EXPECTED: unsat => sound. A 'sat' model would mean an arbitrary derived
;   witness could strengthen the forall -- impossible.
(set-logic UFNIA)
(define-fun P () Int 7)
(declare-fun body (Int) Bool)
(declare-fun a () Int)
(declare-fun expr (Int) Int)   ; arbitrary derived expression over free var a

(define-fun ORIG () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P)) (body q))))
(define-fun WEAK () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P))
                        (or (body q) (not (= q (mod (expr a) P)))))))

(assert ORIG)
(assert (not WEAK))
(check-sat)
