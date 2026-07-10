; rule: implies-elim  (walk_implies)
; contract: equivalence (boolean).  (a => b) -> Or(negate(a), b)
; check: negation of ((a=>b) <=> (or (not a) b)). expect UNSAT = sound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (not (= (=> a b) (or (not a) b))))
(check-sat)
