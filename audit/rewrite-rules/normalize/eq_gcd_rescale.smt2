; rule: eq_gcd_rescale  (normalize._NormalizeWalker.walk_equals, non-modular branch)
; contract: equivalence  (A <=> B)
; transform: (= (lhs-rhs) 0) -> (= ((lhs-rhs)/g) 0), g = gcd of coeffs, and the
;   leading coefficient is forced POSITIVE (sign flip is allowed for "= 0").
; check two instances over Z (P not involved):
;   (a) diff =  6x+9y, g=3, rep =  2x+3y   (no sign flip)
;   (b) diff = -6x-9y, lc<0 so g=-3, rep = 2x+3y   (sign flipped -- fine for =0)
;   Assert either equivalence fails for some integers x,y.
; EXPECTED: unsat  (=> SOUND). Dividing "=0" by a nonzero constant (or negating)
;   preserves the zero set exactly. A 'sat' model would be a gained/lost root.
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (or
  (not (= (= (+ (* 6 x) (* 9 y)) 0)
          (= (+ (* 2 x) (* 3 y)) 0)))
  (not (= (= (+ (* (- 6) x) (* (- 9) y)) 0)
          (= (+ (* 2 x) (* 3 y)) 0)))))
(check-sat)
