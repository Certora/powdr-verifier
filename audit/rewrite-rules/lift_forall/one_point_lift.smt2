; rule slug: one_point_lift
; contract: equisat (definitional extension via the one-point / universal-instantiation rule)
;
; What lift_forall does (LiftForallWalker.walk_forall + simplify_lift_forall):
;   Given an assertion   (forall (q ...) (or ... (not (= q e)) ... R))
;   where e mentions no still-quantified variable, it:
;     * removes the disjunct (not (= q e)) from the body,
;     * drops q from the quantifier prefix,
;     * declares q as a fresh top-level symbol and asserts (= q e),
;     * re-emits the (possibly still-quantified) remaining Or as the assertion.
;   Net effect on a single-qvar forall:
;     (forall (q) (or (not (= q e)) R(q)))   -->   (and (= q e) R(q))  with q a fresh global.
;
; The input body disjunct is exactly the shape produced by simplify_skolem
; (a pinning witness (not (= q other))). One-point rule:
;     (forall (q) (or (not (= q e)) R(q)))  <=>  R(e)
;   and the transformed script { declare q ; assert (= q e) ; assert R(q) } is
;   satisfiable iff (exists q. q = e /\ R(q)) iff R(e), with q fresh.
;   Hence the transform is equivalent (a fortiori equisat / unsat-preserving in
;   both directions) -- SOUND -- provided q is genuinely fresh (see the
;   cross_assertion_capture validator for the freshness caveat).
;
; CHECK: negation of the equivalence  (forall q. (q != e \/ R q)) <=> R(e).
; EXPECTED: unsat  => rule is sound (the one-point collapse preserves meaning).
; A 'sat' model would exhibit an interpretation of R and e under which the
; lifted form disagrees with the quantified form, i.e. an unsound collapse.
(set-logic UFLIA)
(declare-fun e () Int)
(declare-fun R (Int) Bool)
(define-fun ORIG () Bool (forall ((q Int)) (or (not (= q e)) (R q))))
(define-fun XFORM () Bool (R e))
(assert (not (= ORIG XFORM)))
(check-sat)
