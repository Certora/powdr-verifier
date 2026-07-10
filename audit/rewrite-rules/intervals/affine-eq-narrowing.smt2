; rule: affine_eq  (_refine_affine_eq, reasoner.py:237-287)
; contract: sound narrowing. From an affine equality a==b, isolate each symbol:
;   const + sum coeff_i*sym_i = 0 => sym = -other/coeff, narrow to floor/ceil of that range.
; INSTANCE: x in [0,10], x + y = 12.  For y: y = 12 - x in [2,12].
; CHECK: is (2 <= y <= 12) implied by (0<=x<=10 and x+y=12)?
; EXPECTED: unsat => sound (derived two-sided bound is implied; a sat model would be a
;   counterexample where the equality holds yet y falls outside [2,12]).
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 10))
(assert (= (+ x y) 12))
(assert (not (and (<= 2 y) (<= y 12))))
(check-sat)
