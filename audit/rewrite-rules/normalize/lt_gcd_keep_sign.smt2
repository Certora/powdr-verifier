; rule: lt_gcd_keep_sign  (normalize._NormalizeWalker.walk_lt, non-modular)
; contract: equivalence  (A <=> B)
; transform: (< lhs rhs) -> (< ((lhs-rhs)/g) 0), g = POSITIVE gcd of coeffs.
;   Uses _rescale_gcd_keep_sign: NEVER negates (sign is load-bearing for "<").
; check two instances over Z:
;   (a) diff =  6x+9y, g=3, rep =  2x+3y
;   (b) diff = -6x-9y, g=3 (kept positive), rep = -2x-3y   (NOT flipped)
;   Assert either equivalence fails.
; EXPECTED: unsat  (=> SOUND). Dividing "< 0" by a POSITIVE constant preserves
;   the order. A 'sat' model = order changed = UNSOUND.
; REGRESSION NOTE: the OLD buggy code used _rescale_gcd (positive-leading), which
;   for instance (b) would emit rep = +2x+3y, flipping the relation. Swapping the
;   second rep to (+ (* 2 x)(* 3 y)) below makes this file SAT -- the bug.
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (or
  (not (= (< (+ (* 6 x) (* 9 y)) 0)
          (< (+ (* 2 x) (* 3 y)) 0)))
  (not (= (< (+ (* (- 6) x) (* (- 9) y)) 0)
          (< (+ (* (- 2) x) (* (- 3) y)) 0)))))
(check-sat)
