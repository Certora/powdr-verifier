; rule slug: not-not
; pass: nnf  (_negate: if formula.is_not(): return formula.arg(0))
; contract: equivalence (boolean)
; transform: (not (not f)) -> f   (double-negation elimination)
; check via nested case: (not (not (and a b))) should equal (and a b).
; EXPECTED: unsat => sound.
;   A 'sat' model would be a polarity flip from mishandled double negation.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (not (= (not (not (and a b))) (and a b))))
(check-sat)
