; rule slug: witness-substitution-identity (BabyBear P variant)
; pass: skolem-aux
; contract: equivalence (distributivity of the q_i := free_var substitution mod P)
; Same check as witness-substitution-identity.smt2 but with the real BabyBear
; prime P = 2013265921. Distributivity is prime-independent so this is also
; valid; included per audit protocol. May be slower but should still be unsat.
; EXPECTED: unsat.

(set-logic QF_NIA)
(define-fun P () Int 2013265921)
(declare-fun fv () Int)
(declare-fun a0 () Int)
(declare-fun a1 () Int)
(declare-fun c () Int)
(declare-fun cmp () Int)

(define-fun expanded_sub () Int (+ (* fv a0) (* fv a1) (* c cmp)))
(define-fun collapsed  () Int (+ (* fv (+ a0 a1)) (* c cmp)))

(assert (not (= (mod expanded_sub P) (mod collapsed P))))
(check-sat)
