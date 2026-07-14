; rule slug: polarity-assumption-load-bearing  (adversarial; applies to ALL three contributors)
; contract: demonstrates the load-bearing precondition (forall must be POSITIVE / post-NNF)
;
; The three contributors are sound ONLY because simplify_skolem runs after nnf,
; so every `forall` node occurs in positive polarity and appending disjuncts to
; its body weakens the whole assertion. This file shows what breaks if that
; invariant were violated: if the forall were under a negation, the same
; disjunct-append STRENGTHENS the assertion instead, so rewritten-UNSAT would
; NOT imply original-UNSAT (unsound).
;
; NEG_ORIG = (not (forall q. body(q)))          [forall in NEGATIVE polarity]
; NEG_WEAK = (not (forall q. (body(q) or q!=w))) [same append, now under the not]
; We check NEG_ORIG ==> NEG_WEAK by asserting (and NEG_ORIG (not NEG_WEAK)).
;
; EXPECTED: sat  => in negative polarity the transform is NOT unsat-preserving,
;   confirming the NNF/positive-polarity ordering requirement is essential.
;   (This is NOT a bug in the modules; it is a witness that the pass-ordering
;    precondition documented in skolem.py is load-bearing.)
(set-logic UFNIA)
(define-fun P () Int 7)
(declare-fun body (Int) Bool)
(declare-fun w () Int)

(define-fun NEG_ORIG () Bool
  (not (forall ((q Int)) (=> (and (>= q 0) (< q P)) (body q)))))
(define-fun NEG_WEAK () Bool
  (not (forall ((q Int)) (=> (and (>= q 0) (< q P))
                             (or (body q) (not (= q (mod w P))))))))

(assert NEG_ORIG)
(assert (not NEG_WEAK))
(check-sat)
