; rule: array-eq-extensionality (walk_equals: (= arr1 arr2) -> forall i. read=read)
; contract: equivalence (array extensionality)
; check: (= a b) <=> (forall i. (select a i) = (select b i)).
;        Assert the two are NOT boolean-equivalent.
; EXPECTED: unsat (sound; holds under array extensionality, which z3 provides).
;           sat would mean the pointwise rewrite is not equivalent to array =.
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (not (= (= a b)
                (forall ((i Int)) (= (select a i) (select b i))))))
(check-sat)
