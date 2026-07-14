; rule: demorgan-or  (_negate on Or node, used by walk_not)
; contract: equivalence (boolean).  Not(Or(a,b,c)) -> And(Not a, Not b, Not c)
; check: negation of (A <=> B). expect UNSAT = sound.
; a sat model would be a boolean assignment where De Morgan fails => unsound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(define-fun A () Bool (not (or a b c)))
(define-fun B () Bool (and (not a) (not b) (not c)))
(assert (not (= A B)))
(check-sat)
