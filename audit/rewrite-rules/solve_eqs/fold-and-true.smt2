; rule slug: fold-and-true
; pass: solve_eqs  (_FoldRefl.walk_and)
; contract: EQUIVALENCE  ( (and ... True ...) -> drop True ; ()->True ; single->itself )
;
; RULE: drop True conjuncts; empty conjunction -> True; singleton -> the element.
;   Sound iff True is the identity element of conjunction (it is).
;
; Check all three shapes at once against their folded forms.
; EXPECTED: unsat => folding preserves meaning => rule SOUND.
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
; drop-True: (and p True q) == (and p q)
(define-fun lhs1 () Bool (and p true q))
(define-fun rhs1 () Bool (and p q))
; empty-> True: (and True True) == True
(define-fun lhs2 () Bool (and true true))
(define-fun rhs2 () Bool true)
; singleton: (and p True) == p
(define-fun lhs3 () Bool (and p true))
(define-fun rhs3 () Bool p)
(assert (not (and (= lhs1 rhs1) (= lhs2 rhs2) (= lhs3 rhs3))))
(check-sat)
