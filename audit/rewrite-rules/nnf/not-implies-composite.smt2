; rule: composite  (walk_implies then walk_not: exercises _negate over Or)
; Not(a => b) is converted bottom-up: (a=>b)->Or(neg a, b), then
;   walk_not/_negate over Or -> And(negate(neg a), negate b) = And(a, not b).
; contract: equivalence (boolean).  Not(a=>b) -> And(a, Not b)
; check: negation of equivalence. expect UNSAT = sound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (not (= (not (=> a b)) (and a (not b)))))
(check-sat)
