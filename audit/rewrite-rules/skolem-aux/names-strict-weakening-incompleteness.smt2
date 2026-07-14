; rule slug: names-strict-weakening-incompleteness  (companion to names-same-name-instantiation)
; contract: documents that the rule is a PROPER weakening (not equivalence)
;
; WHAT IS CHECKED
;   The reverse implication  WEAK ==> ORIG  is NOT valid. We assert
;   (and WEAK (not ORIG)); a model proves the rewrite can turn an
;   UNSAT-yielding original into a SAT weakened form => the pass is
;   incomplete (may report spurious sat / counterexample) but that is
;   the acknowledged trade-off, NOT unsoundness.
;
; EXPECTED: sat  => confirms strict weakening (incomplete, still sound for unsat-proving).
(set-logic UFNIA)
(define-fun P () Int 7)
(declare-fun body (Int) Bool)
(declare-fun other () Int)

(define-fun ORIG () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P)) (body q))))
(define-fun WEAK () Bool
  (forall ((q Int)) (=> (and (>= q 0) (< q P))
                        (or (body q) (not (= q (mod other P)))))))

(assert WEAK)
(assert (not ORIG))
(check-sat)
