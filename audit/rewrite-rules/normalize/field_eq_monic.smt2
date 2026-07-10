; rule: field_eq_monic  (normalize._NormalizeWalker.walk_equals, modular branch)
; contract: equivalence  (A <=> B)
; transform: (= (mod L P) 0)  ->  (= (mod (lc^{-1} * L mod P) P) 0)
;   i.e. multiply the diff polynomial by the modular inverse of its leading
;   coefficient so the leading coeff becomes 1 (monic canonical form).
; check: for the concrete instance L = 3x+6, P=97, lc=3, inv(3)=65 mod 97,
;   rep = 65*3 x + 65*6  (mod 97) = 1*x + 2 = x+2.
;   Assert the two field-equalities are NOT equivalent for some integer x.
; EXPECTED: unsat  (=> rule is SOUND / equivalence holds).
;   A 'sat' model would give an x where L=0 mod P but rep!=0 mod P (or vice
;   versa) -- a solution gained or lost by the monic rescale = UNSOUND.
(set-logic QF_NIA)
(declare-const x Int)
(define-fun P () Int 97)
(define-fun L  () Int (+ (* 3 x) 6))
(define-fun REP () Int (+ x 2))
(assert (not (= (= (mod L P) 0)
                (= (mod REP P) 0))))
(check-sat)
