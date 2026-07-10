; rule: store-nonstore   (_reduce lines 175-184)
; A -> B :  (= (store A k v) b)   with constant k, b a non-store array symbol
;   e1 = (= v (select b k))       ; rb_at_idx = _read(b,k)
;   base_eq = (= A b)             ; reduce(A,b), b a bare symbol
;   B = (and e1 base_eq)
; correct: store(A,k,v)=b  <=>  b[k]=v AND (A,b agree at all j != k).
;   but (= A b) forces A[k]=b[k]=v too, NOT required by original (A[k] is overwritten).
; CHECK strengthening: Original AND (not Rewrite).
; EXPECTED: sat  (counterexample where A[k] != b[k] = UNSOUND for distinct bases)
(set-logic ALL)
(declare-const A (Array Int Int))
(declare-const b (Array Int Int))
(declare-const k Int)
(declare-const v Int)
(assert (= (store A k v) b))
(assert (not (and (= v (select b k)) (= A b))))
(check-sat)
(get-value (k A b))
