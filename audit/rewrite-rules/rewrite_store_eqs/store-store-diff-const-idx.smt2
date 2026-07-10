; rule: store-store-diff-const-idx   (_reduce lines 156-170)
; A -> B :  (= (store A 0 v) (store B 1 v2))   with distinct constant indices 0 != 1
;   e1 = (= v (select B 0))        ; rb_at_a = _read(b,0) = B[0]
;   e2 = (= (select A 1) v2)       ; ra_at_b = _read(a,1) = A[1]
;   base_eq = (= A B)              ; reduce(A,B), distinct base symbols
;   B = (and e1 e2 base_eq)
; contract: rewrite must be WEAKER-or-equal for verifier soundness.
; correct decomposition: v=B[0] AND A[1]=v2 AND (A,B agree at all j not in {0,1}).
;   but base_eq (= A B) also forces A[0]=B[0] and A[1]=B[1], NOT required by original.
; CHECK strengthening: Original AND (not Rewrite).
; EXPECTED: sat  (counterexample where A,B differ at index 0 or 1 = UNSOUND for distinct bases)
(set-logic ALL)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const v Int)
(declare-const v2 Int)
(assert (= (store A 0 v) (store B 1 v2)))
(assert (not (and (= v (select B 0)) (= (select A 1) v2) (= A B))))
(check-sat)
(get-value (A B))
