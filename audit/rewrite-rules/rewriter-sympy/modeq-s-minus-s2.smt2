; rule: modeq-s-minus-s2   (rewrite_mod_equality case 3 / case 4 -- DORMANT)
; source: rewrites_sympy.py rewrite_mod_equality:
;     if m := expr.match(s - s2):            return Eq(m[s], m[s2])
;     if m := expr.match(s + (P-1)*s2):      return Eq(m[s], m[s2])   ; (p-1)==-1 mod p
; transform: Mod(s - s2, p) == 0  -->  s == s2   (exact equality, drops the modulus)
; contract: EQUIVALENCE.
; what is checked HERE (no range on s, s2): Mod(s - s2, 7)==0  <=>  s == s2
; EXPECTED: sat  -- witness s=7, s2=0 (7-0=7=0 mod7, congruent) but s != s2.
;   'sat' => not an equivalence; sound only when BOTH s and s2 are field-range
;   constrained to [0,p). Same dropped-modulus / conditional-soundness class as the
;   choice-solved-roots rule.
(set-logic QF_NIA)
(declare-fun s () Int)
(declare-fun s2 () Int)
(define-fun A () Bool (= (mod (- s s2) 7) 0))
(define-fun B () Bool (= s s2))
(assert (not (= A B)))
(check-sat)
(get-value (s s2))
