; rule: constarray-constarray   (_reduce lines 198-202)
; A -> B :  (= (as const (Array Int Int) v1) (as const (Array Int Int) v2)) -> (= v1 v2)
; contract: equivalence.  Index domain Int is nonempty so two const arrays are equal
;   iff their default values are equal.
; CHECK: (Original xor Rewrite) unsatisfiable, i.e. assert (not (<=> Original Rewrite)).
; EXPECTED: unsat  (unsat = sound equivalence)
(set-logic ALL)
(declare-const v1 Int)
(declare-const v2 Int)
(assert (not (= (= ((as const (Array Int Int)) v1) ((as const (Array Int Int)) v2))
                (= v1 v2))))
(check-sat)
