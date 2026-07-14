; rule: field_eq_monic (multivariable / nonlinear stress)
;   normalize._NormalizeWalker.walk_equals, modular branch -> _rescale_monic
; contract: equivalence  (A <=> B)
; transform: (= (mod L P) 0) -> (= (mod (lc^{-1} * L mod P) P) 0)
;   Here L = 3*x*y + 6*x + 9, P=97. Graded-lex leading monomial is x*y, lc=3.
;   inv(3) mod 97 = 65.  rep = 65*(3xy+6x+9) mod 97 = xy + 2x + 3
;     (390 mod 97 = 2 ; 585 mod 97 = 3).
; Checks the monic rescale is a field UNIT multiply (nonzero constant), which
;   preserves the mod-P zero set exactly even at degree>1 / multiple vars, and
;   that the leading-monomial selection does not affect soundness.
; EXPECTED: unsat  (=> SOUND). A 'sat' model = an (x,y) where exactly one of the
;   two field-equalities holds = a root gained/lost by the rescale = UNSOUND.
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(define-fun P () Int 97)
(define-fun L   () Int (+ (* 3 (* x y)) (* 6 x) 9))
(define-fun REP () Int (+ (* x y) (* 2 x) 3))
(assert (not (= (= (mod L P) 0)
                (= (mod REP P) 0))))
(check-sat)
