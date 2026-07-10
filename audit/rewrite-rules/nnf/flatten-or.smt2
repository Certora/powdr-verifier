; rule: flatten-or  (_flatten_or: nested Or flattened; []->FALSE; [a]->a)
; contract: equivalence (boolean).  Or(a, Or(b,c)) -> Or(a,b,c)
; check: negation of equivalence. expect UNSAT = sound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (not (= (or a (or b c)) (or a b c))))
(check-sat)
