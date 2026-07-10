; rule: ineq_sym_upper (strict)  (_refine_from_ineq, reasoner.py:398-406)
; contract: sound narrowing. sym < c (integers) => sym <= c-1.
; INSTANCE: x < 5 => x <= 4.
; CHECK: is (x <= 4) implied by (x < 5) over integers?
; EXPECTED: unsat => sound.
(set-logic QF_LIA)
(declare-const x Int)
(assert (< x 5))
(assert (not (<= x 4)))
(check-sat)
