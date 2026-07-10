; rule: modeq-s-minus-c   (rewrite_mod_equality cases 1/2 -- DORMANT: rewrite_mod_equality
;   is imported by __init__.py but NOT placed in REWRITES_SYMPY, so it is not applied.)
; source: rewrites_sympy.py rewrite_mod_equality:
;     if m := expr.match(s - c):  return Eq(m[s], Mod(m[c], modulus))
;     if m := expr.match(c - s):  return Eq(m[s], Mod(m[c], modulus))
; transform: Mod(s - c, p) == 0  -->  s == (c mod p)     (exact integer equality)
;   Unlike the c+(p-1)*s sibling this DOES reduce the constant (Mod(c,p)), so the
;   only soundness gap is the dropped modulus on s (integer eq vs congruence).
; contract: EQUIVALENCE.
; what is checked HERE (no range on s): Mod(s - 3, 7)==0  <=>  s == 3
; EXPECTED: sat  -- witness s=10 (10-3=7=0 mod7, congruent) but s != 3.
;   'sat' => not an equivalence over Z; sound ONLY when s is field-range constrained
;   to [0,p). Same conditional-soundness class as choice-solved-roots-range.
(set-logic QF_NIA)
(declare-fun s () Int)
(define-fun A () Bool (= (mod (- s 3) 7) 0))
(define-fun B () Bool (= s 3))
(assert (not (= A B)))
(check-sat)
(get-value (s))
