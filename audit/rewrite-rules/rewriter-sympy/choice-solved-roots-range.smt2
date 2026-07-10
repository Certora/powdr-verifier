; rule: choice-solved-roots-range  (THE KEY FINDING)
; source: rewrites.py rewrite_choice_simple -> _solved_roots -> roots_with_range;
;         rewrites_sympy.py rewrite_choice -> _solved_roots branch
; transform: Mod(e, p) == 0, when every factor of e is linear in ONE symbol x,
;            -->  (Or_r  x == r) AND (min(roots) <= x) AND (x <= max(roots))
;   Crucially the output uses EXACT integer equality x == r (r in [0,p)) and adds
;   bounds -- it DROPS the modulus.
; contract: EQUIVALENCE (equality atom is a positive circuit hypothesis in the VC;
;   soundness needs: original-SAT => rewritten-SAT, i.e. the rewrite must not
;   strengthen the hypothesis and delete a counterexample).
; what is checked HERE (no range axiom on x): is  Mod(x*(x-1),7)==0  <=>  ((x=0 or x=1) and 0<=x<=1) ?
; EXPECTED: sat  -- a counterexample (e.g. x = 7) satisfies the ORIGINAL congruence
;   (7*6 = 42 = 0 mod 7) but FALSIFIES the rewritten form (x != 0,1 and x > 1).
;   'sat' means the rewrite is NOT an equivalence: it manufactures UNSAT (false PASS)
;   for any model where the solved variable x lies OUTSIDE [0,p). The rule is therefore
;   sound ONLY under an external invariant  0 <= x < p , which the rewrite never checks.
;   (Range axioms are added only for symbols matching '@<digits>' in simplify_bounds.)
(set-logic QF_NIA)
(declare-fun x () Int)
(define-fun A () Bool (= (mod (* x (- x 1)) 7) 0))
(define-fun B () Bool (and (or (= x 0) (= x 1)) (<= 0 x) (<= x 1)))
(assert (not (= A B)))
(check-sat)
(get-value (x))
