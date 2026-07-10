; rule: le_gcd_keep_sign  (normalize._NormalizeWalker.walk_le, non-modular)
; contract: equivalence  (A <=> B)
; transform: (<= lhs rhs) -> (<= ((lhs-rhs)/g) 0), g = POSITIVE gcd (no negation).
; check two instances over Z:
;   (a) diff =  6x+9y, g=3, rep =  2x+3y
;   (b) diff = -6x-9y, g=3, rep = -2x-3y  (sign preserved)
; EXPECTED: unsat  (=> SOUND). Dividing "<= 0" by a positive constant preserves
;   the (non-strict) order. 'sat' would be an order change = UNSOUND.
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (or
  (not (= (<= (+ (* 6 x) (* 9 y)) 0)
          (<= (+ (* 2 x) (* 3 y)) 0)))
  (not (= (<= (+ (* (- 6) x) (* (- 9) y)) 0)
          (<= (+ (* (- 2) x) (* (- 3) y)) 0)))))
(check-sat)
