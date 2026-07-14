; rule slug: names-same-name-instantiation  (skolem_names.contribute)
; contract: unsat-preserving (weakening of a positively-occurring forall)
;
; WHAT THE RULE DOES
;   For a positive `(forall ((q Int)) body(q))` (post-NNF), if there is a
;   declared free symbol `other` with the same stripped name and type as qvar
;   `q`, it pins q := other. skolem.emit_disjuncts then rewrites the forall to
;       (forall ((q Int)) (or body(q) (not (= q (mod other P)))))
;   which is logically the single instance  body(mod other P).
;
; WHAT IS CHECKED HERE
;   The transform must satisfy: rewritten UNSAT => original UNSAT.
;   Since the forall is positive, that holds iff  original ==> rewritten
;   (i.e. rewritten is weaker). We check that implication is VALID by asserting
;   its negation:  (and ORIG (not WEAK)).  `body` is an uninterpreted predicate
;   so this covers every possible body. Field ranged with small P=7.
;
; EXPECTED: unsat  => sound (original always implies the weakened form).
;   A 'sat' model would exhibit a field-ranged body under which ALL q satisfy
;   body(q) yet body(other mod P) fails -- a contradiction, i.e. the rewrite
;   would be strengthening (unsound). None should exist.
(set-logic UFNIA)
(define-fun P () Int 7)
(declare-fun body (Int) Bool)
(declare-fun other () Int)

; ORIG: forall q in field. body(q)
(define-fun ORIG () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P)) (body q))))

; WEAK: forall q in field. (body(q) or q != (other mod P))
(define-fun WEAK () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P))
                        (or (body q) (not (= q (mod other P)))))))

(assert ORIG)
(assert (not WEAK))
(check-sat)
