; rule slug: one-point-elim-array
; pass: solve_eqs
; contract: equisat. Same one-point rule but for an ARRAY-typed symbol -- the
;   motivating case is the pin equality (= before-memory after-memory) between
;   two (Array Int Int) symbols, and the const-array RHS ((as const T) v).
;
; WHAT IS CHECKED: the one-point rule schema over the array sort.
;   P ((Array Int Int) Int) Bool  = arbitrary body Phi(x, y).
;   e (Int) (Array Int Int)       = witness (array-valued), depends only on y
;                                   (encodes "e does not mention x").
;   Claim: (exists x. (x = e(y)) /\ Phi(x,y)) <=> Phi(e(y), y).
;
; EXPECTED VERDICT: unsat = rule is SOUND for array substitution too.
;   (Array equality is extensional structural equality; one-point rule holds for
;   any sort, so this must be unsat regardless of the element/index sorts.)
;   A 'sat' model would witness disagreement = unsound array substitution.

(set-logic ALL)
(declare-fun P ((Array Int Int) Int) Bool)
(declare-fun e (Int) (Array Int Int))

(assert (not
  (forall ((y Int))
    (= (exists ((x (Array Int Int))) (and (= x (e y)) (P x y)))
       (P (e y) y)))))

(check-sat)
