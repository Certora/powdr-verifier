; rule: eq-refl   (_reduce line 132)   contract: equivalence
; A -> B :  (= a a)  ->  True
; check: reflexive array equality is valid. assert its negation.
; EXPECTED: unsat  (unsat = sound; sat would mean (= a a) can be false)
(set-logic ALL)
(declare-const a (Array Int Int))
(assert (not (= a a)))
(check-sat)
