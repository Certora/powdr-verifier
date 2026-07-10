; rule slug: expanded-witness-universal-instantiation (CORE soundness check)
; contract: unsat-preserving (verifier direction: rewritten UNSAT => original UNSAT,
;           i.e. must never turn a SAT / counterexample-bearing VC into UNSAT).
; pass: witness (src/simplify/witness.py, WitnessSubstituter.walk_forall)
;
; WHAT THE PASS DOES:
;   Replaces a positive top-level  (forall (q0 q1 ...) Body(q0,q1,...))
;   by the single ground instance  Body(fv,fv,...)   where fv is the collapsed
;   witness's free_var, dropping the substituted qvars from the quantifier
;   (dropping the quantifier entirely when all qvars are substituted).
;   In verifier.py the ONLY forall is the positive conjunct
;     And(before, ForAll(q, Or(Not(after), Not(io))), ...).
;
; WHAT THIS CHECKS: universal instantiation is a WEAKENING in a positive position:
;   (forall q. P(q))  ==>  P(fv).
;   If this implication is valid, then replacing the forall conjunct by the
;   instance can only ADD models (weaken the VC), so it never turns SAT into
;   UNSAT => sound (may only lose completeness).
;
; EXPECTED VERDICT: unsat  (=> implication valid => weakening is sound).
;   A 'sat' model would be an assignment where the universal holds yet the
;   instance fails -- impossible for genuine instantiation; would indicate the
;   substitution point fv escapes the quantifier domain (unsoundness).
;
; P = 7 (tiny field). Field-Int domain modeled by mod-7 equality; qvars are Int
; (unbounded), matching the real encoding where fv is a plain Int symbol.
(set-logic UFNIA)
(declare-fun f0 () Int)
(declare-fun f1 () Int)
(declare-fun cmp () Int)
(declare-fun fv () Int)
; P(q0,q1) :=  q0*f0 + q1*f1 - cmp == 0 (mod 7)   -- the expanded-witness equation
(assert (forall ((q0 Int) (q1 Int))
          (= (mod (- (+ (* q0 f0) (* q1 f1)) cmp) 7) 0)))
; negation of the ground instance P(fv,fv)
(assert (not (= (mod (- (+ (* fv f0) (* fv f1)) cmp) 7) 0)))
(check-sat)
