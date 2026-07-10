; rule: choice-quadratic-roots
; source: rewrites.py _quadratic_linear_factors + _solved_roots -> roots_with_range;
;         rewrites_sympy.py rewrite_choice -> _solved_quadratic branch
; transform: Mod(a*x^2+b*x+c, p)==0 (a!=0), disc a QR -->
;            (Or_r x==r) AND min<=x<=max, with r the two modular roots.
;   Same exact-equality-drops-mod shape as choice-solved-roots-range, PLUS it validates
;   the modular-root computation (_quadratic_roots_mod / sqrt_mod).
; instance: x^2 - 1 over P=7, roots {1,6}.
; contract: EQUIVALENCE. what is checked HERE (no range on x):
;   Mod(x^2-1,7)==0  <=>  ((x=1 or x=6) and 1<=x<=6)
; EXPECTED: sat  -- witness x=8 (64-1=63=0 mod7) satisfies original but not rewritten
;   (x>6, x!=1,6). Demonstrates the SAME conditional-soundness / dropped-modulus issue.
;   The companion .with-range file shows it is unsat (hence roots {1,6} are correct AND
;   the rule is sound) once 0<=x<7 is assumed.
(set-logic QF_NIA)
(declare-fun x () Int)
(define-fun A () Bool (= (mod (- (* x x) 1) 7) 0))
(define-fun B () Bool (and (or (= x 1) (= x 6)) (<= 1 x) (<= x 6)))
(assert (not (= A B)))
(check-sat)
(get-value (x))
