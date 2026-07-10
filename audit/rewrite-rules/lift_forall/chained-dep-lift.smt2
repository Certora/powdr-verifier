; rule slug: chained-dep-lift
; pass: lift_forall
; contract: equivalence
;
; WHAT: the iterative fixpoint (while progressed) can pin q1=e first,
;   which removes q1 from the 'qvars' set; then a second disjunct
;   (not (= q2 f(q1))) becomes eligible because _qvar_deps(f(q1),{q2})
;   no longer sees q1 (already lifted). So q2 is pinned to f(q1) where q1
;   is now the top-level constant pinned to e.
;     forall q1,q2. ( q1!=e | q2!=f(q1) | R(q1,q2) )
;   becomes:  q1=e ; q2=f(q1) ; R(q1,q2)   (q1,q2 free)
;   which should equal R(e, f(e)).
;
; This is the delicate case the hint flags (scope of a var used inside a
; later pin's expr). It is sound BECAUSE the earlier-lifted var is pinned
; to exactly the same value, so f(q1) = f(e).
;
; CHECK: assert SRC differs from the substituted form -> expect UNSAT.
; EXPECTED VERDICT: unsat => sound.
;   'sat' would reveal that chained pinning substitutes an inconsistent
;   value for the intermediate variable = unsound.

(set-logic UFLIA)
(declare-fun e () Int)
(declare-fun f (Int) Int)
(declare-fun R (Int Int) Bool)

(define-fun SRC () Bool
  (forall ((q1 Int) (q2 Int))
    (or (not (= q1 e)) (not (= q2 (f q1))) (R q1 q2))))

; peel result with both pins, q1=e and q2=f(q1)=f(e):
(define-fun DST () Bool (R e (f e)))

(assert (not (= SRC DST)))
(check-sat)
