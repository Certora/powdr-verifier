; rule: demorgan-and  (_negate on And node, used by walk_not)
; contract: equivalence (boolean).  Not(And(a,b,c)) -> Or(Not a, Not b, Not c)
; check: negation of (A <=> B). expect UNSAT = sound.
; a sat model would be a boolean assignment where De Morgan fails => unsound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(define-fun A () Bool (not (and a b c)))
(define-fun B () Bool (or (not a) (not b) (not c)))
(assert (not (= A B)))
(check-sat)
