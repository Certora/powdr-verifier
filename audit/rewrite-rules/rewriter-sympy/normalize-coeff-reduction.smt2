; rule: normalize-coeff-reduction
; source: rewrites_sympy.py normalize(e) = expand(e, modulus=P); used only INSIDE
;   rewrite_choice as Mod(normalize(f), c) == 0 for each disjunct factor f.
; transform: reduce polynomial coefficients modulo p (and expand), while the result
;   stays under an outer Mod(., p) == 0.  E.g. Mod(x + 8*y + 10, 7)==0 is emitted as
;   Mod(x + y + 3, 7)==0   (8 ≡ 1, 10 ≡ 3 mod 7).
; contract: EQUIVALENCE.
; what is checked: reducing coefficients mod p preserves the congruence, for ALL integers.
;   Mod(x + 8*y + 10, 7)==0  <=>  Mod(x + y + 3, 7)==0
; EXPECTED: unsat  (sound). Coefficient reduction mod p is value-preserving under Mod(.,p).
;   A 'sat' model would mean reduction changed the congruence class -> would be unsound.
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x (- 30))) (assert (<= x 30))
(assert (>= y (- 30))) (assert (<= y 30))
(define-fun A () Bool (= (mod (+ x (+ (* 8 y) 10)) 7) 0))
(define-fun B () Bool (= (mod (+ x (+ y 3)) 7) 0))
(assert (not (= A B)))
(check-sat)
