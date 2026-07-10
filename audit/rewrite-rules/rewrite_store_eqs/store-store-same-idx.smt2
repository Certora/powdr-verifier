; rule: store-store-same-idx   (_reduce lines 149-154)
; A -> B :  (= (store A k v) (store B k v2))
;        -> (and (= v v2) (= A B))          [base_eq = reduce(A,B) = (= A B) when bases differ]
; contract for VERIFIER SOUNDNESS: rewrite must be WEAKER-or-equal, i.e. Original => Rewrite,
;   so that no satisfying model (counterexample) of the assertion set is lost.
;   (a rewrite that removes models can turn SAT into UNSAT = false PASS = UNSOUND).
; CHECK for strengthening:  Original  AND  (not Rewrite).
;   sat  => there is a model of Original that Rewrite rejects => Rewrite is STRICTLY STRONGER
;          => UNSOUND (this is the base-equality over-constraint: original only needs A,B to
;          agree OFF index k, but (= A B) forces agreement AT k too).
; EXPECTED: sat  (sat = counterexample = UNSOUND as written for distinct bases)
(set-logic ALL)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const k Int)
(declare-const v Int)
(declare-const v2 Int)
; original store equality
(assert (= (store A k v) (store B k v2)))
; negation of the produced rewrite
(assert (not (and (= v v2) (= A B))))
(check-sat)
(get-value (k A B))
