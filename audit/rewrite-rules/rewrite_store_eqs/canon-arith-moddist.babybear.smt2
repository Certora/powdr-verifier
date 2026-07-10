; rule: canon-arith mod-distribution -- BabyBear P variant (may be slow / timeout).
; same check as canon-arith-moddist.smt2 with real P = 2013265921.
; EXPECTED: unsat  (mod distribution is an exact integer identity for any positive modulus).
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (mod (+ (* x 65536) y) 2013265921)
                (mod (+ (* 65536 (mod x 2013265921)) (mod y 2013265921)) 2013265921))))
(check-sat)
