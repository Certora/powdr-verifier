; rule slug: array_eq_pointwise
; pass: define_inner_array   (_SubSelectWithFnCall.walk_equals)
; contract: equivalence  (relies on ARRAY EXTENSIONALITY)
; transform: an array-typed equality (= a b) in which a or b is a converted array
;   symbol is rewritten to (forall ((i Int)) (= (read a i) (read b i))), where read
;   is a macro-call for converted sides and a plain select otherwise.
; WHAT IS CHECKED: (= a b)  <=>  (forall i. (select a i) = (select b i)).
;   This is the array extensionality axiom, which z3's array theory validates.
; EXPECTED: unsat (sound). sat would mean the pointwise form disagrees with true
;   array equality in some model -> the rewrite could flip sat/unsat -> unsound.
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= (= a b)
                (forall ((i Int)) (= (select a i) (select b i))))))
(check-sat)
