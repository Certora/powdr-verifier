; rule: double-neg  (_negate: if formula.is_not(): return formula.arg(0))
; contract: equivalence (boolean).  Not(Not a) -> a
; check: negation of (Not(Not a) <=> a). expect UNSAT = sound.
(set-logic QF_UF)
(declare-const a Bool)
(assert (not (= (not (not a)) a)))
(check-sat)
