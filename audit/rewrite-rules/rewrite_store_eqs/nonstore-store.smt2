; rule: nonstore-store   (_reduce lines 186-195)   symmetric to store-nonstore
; A -> B :  (= a (store B k v))   with constant k, a a non-store array symbol
;   e1 = (= (select a k) v)       ; ra_at_idx = _read(a,k)
;   base_eq = (= a B)
;   B = (and e1 base_eq)
; correct: a=store(B,k,v) <=> a[k]=v AND (a,B agree at all j != k). (= a B) over-constrains at k.
; CHECK strengthening: Original AND (not Rewrite).
; EXPECTED: sat  (UNSOUND for distinct bases)
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const B (Array Int Int))
(declare-const k Int)
(declare-const v Int)
(assert (= a (store B k v)))
(assert (not (and (= (select a k) v) (= a B))))
(check-sat)
(get-value (k a B))
