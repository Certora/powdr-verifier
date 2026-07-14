; rule: choice-no-roots-false
; source: rewrites.py rewrite_choice_simple (factors==[] -> FALSE via _quadratic_linear_factors==[]);
;         rewrites_sympy.py rewrite_choice (_solved_quadratic with empty roots -> False)
; transform: Mod(q(x), p)==0  -->  FALSE, when q is a quadratic with NO root mod p.
; instance: x^2 + 1 over P=7 (-1 is a non-residue mod 7), so q(x) is never 0 mod 7.
; contract: EQUIVALENCE.
; what is checked: does there exist ANY integer x with Mod(x^2+1,7)==0 ? (i.e. is FALSE correct?)
; EXPECTED: unsat  (sound: no such x for any integer, no range assumption needed).
;   A 'sat' model would exhibit a root the rule wrongly declared nonexistent -> unsound
;   (would turn a satisfiable hypothesis into FALSE).
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (= (mod (+ (* x x) 1) 7) 0))
(check-sat)
