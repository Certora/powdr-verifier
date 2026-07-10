; rule slug: witness-joint-instantiation  (skolem_witness.contribute + collect_candidates)
; contract: unsat-preserving (weakening of a positively-occurring forall)
;
; WHAT THE RULE DOES
;   Pattern-matches a collapsed top-level form  free_var*(a0+..+ak)+..=0  and
;   the expanded in-body form  q0*a0+..+qk*ak+..=0, then pins every matched
;   qvar qi := free_var. With several qvars pinned, emit_disjuncts appends one
;   disjunct per qvar, so the forall becomes
;       (forall (q0 q1) (or body(q0,q1) (not (= q0 (mod w P))) (not (= q1 (mod w P)))))
;   which is logically the joint instance  body(w mod P, w mod P).
;   Soundness does NOT depend on the (heuristic, possibly wrong) match: any
;   disjuncts appended to a positive forall body only weaken it.
;
; WHAT IS CHECKED:  original ==> rewritten (joint weakening) is VALID.
;   assert (and ORIG (not WEAK)).
; EXPECTED: unsat => sound. A 'sat' model would mean pinning a wrong/shared
;   witness could strengthen a multi-variable forall -- impossible.
(set-logic UFNIA)
(define-fun P () Int 7)
(declare-fun body (Int Int) Bool)
(declare-fun w () Int)   ; free_var witness from the collapsed pattern

(define-fun ORIG () Bool
  (forall ((q0 Int) (q1 Int))
    (=> (and (>= q0 0) (< q0 P) (>= q1 0) (< q1 P)) (body q0 q1))))

(define-fun WEAK () Bool
  (forall ((q0 Int) (q1 Int))
    (=> (and (>= q0 0) (< q0 P) (>= q1 0) (< q1 P))
        (or (body q0 q1)
            (not (= q0 (mod w P)))
            (not (= q1 (mod w P)))))))

(assert ORIG)
(assert (not WEAK))
(check-sat)
