; rule: project-ite  (_FlattenWalker._project on ITE)
;   _project((ite c a b), k) = (ite c (_project a k) (_project b k))
; contract: EQUIVALENCE — must equal (select (ite c a b) k).
; EXPECTED: unsat (select distributes over ite).
(set-logic QF_ALIA)
(declare-fun c () Bool)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= (ite c (select a 3) (select b 3))
                (select (ite c a b) 3))))
(check-sat)
