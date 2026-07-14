; rule: modeq-c-plus-negs   (rewrite_mod_equality case 5 -- DORMANT: imported but not
;   wired into REWRITES_SYMPY; audited because it lives in the assigned file and is a
;   latent bug if enabled.)
; source: rewrites_sympy.py rewrite_mod_equality:
;     if m := expr.match(c + (P-1)*s):  return Eq(m[s], m[c])
; transform: Mod(c + (p-1)*s, p) == 0   -->   s == c
;   BUG: c is bound as a raw Integer and returned UNREDUCED (no Mod(c,p)), unlike the
;   sibling cases s-c / c-s which return Eq(s, Mod(c,p)). Since (p-1) == -1 mod p, the
;   congruence is  s == c (mod p), so the canonical rewrite should be s == (c mod p).
; contract: EQUIVALENCE. Here we even ASSERT the field-range invariant 0<=s<p to show the
;   bug is independent of the range issue.
; instance: P=7, c=7 (a value >= p, which can reach this rule because rewrite_mod_equality
;   does NOT normalize/reduce constants first). Original: Mod(7 + 6*s, 7)==0 <=> s==0.
;   Rewrite: s==7, which is UNSAT under 0<=s<7.
; what is checked: Mod(7 + 6*s, 7)==0  <=>  s==7   given 0<=s<7
; EXPECTED: sat  -- witness s=0 satisfies the original (7+0=7=0 mod7) but not s==7.
;   'sat' => the rewrite turns a SATISFIABLE hypothesis into an unsatisfiable one
;   (false PASS). UNSOUND as written.
(set-logic QF_NIA)
(declare-fun s () Int)
(assert (<= 0 s))
(assert (< s 7))
(define-fun A () Bool (= (mod (+ 7 (* 6 s)) 7) 0))
(define-fun B () Bool (= s 7))
(assert (not (= A B)))
(check-sat)
(get-value (s))
