; rule slug: inject-field-range  (BabyBear P variant of the soundness case)
; pass: bounds. CONTRACT: unsat-preserving (sound axiom injection).
; Same check as inject-field-range.smt2 but with the real modulus
; P = 0x78000001 = 2013265921 used by field_symbol (ARGS().field_type.value).
; Confirms the axiom 0<=x<P is entailed for a canonical field element x=(mod y P).
; EXPECTED: unsat (sound). May be slower but should still decide quickly.
(set-logic QF_NIA)
(declare-fun y () Int)
(define-fun P () Int 2013265921)
(define-fun x () Int (mod y P))
(assert (not (and (<= 0 x) (< x P))))
(check-sat)
