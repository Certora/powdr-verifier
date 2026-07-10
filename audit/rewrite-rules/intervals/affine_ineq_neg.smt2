; rule slug: affine_ineq_neg
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_affine_ineq (coeff < 0 branch, lines 336-348)
; contract: unsat-preserving NARROWING. Given an affine inequality and current
;   domains for the OTHER variables, the reasoner narrows a symbol's domain.
;   Sound narrowing requires: every model of (constraint AND other-var domains)
;   must satisfy the derived bound. If not, the narrowing removes real models,
;   which can turn a SAT (counterexample-bearing) assumption set UNSAT -> false PASS.
;
; The rule: for a term  coeff*sym + rest {<=} target_hi  with coeff<0, den=-coeff,
;   the code derives  sym >= ceil((rest.hi - target_hi)/den).
;   It uses rest.HI (the MAX of the rest range). The sound projection uses rest.LO
;   (existential support: choose the smallest rest to keep the constraint feasible).
;
; Concrete instance encoded here (matches the code exactly):
;   constraint  x <= y   (integer, no mod, P irrelevant)
;   assumed domain  0 <= x <= 10   (so rest = dom(x) = [0,10], h.hi = 10)
;   derived (by the buggy branch)  y >= 10.
;
; CHECK: is the derived bound  y >= 10  actually IMPLIED by (0<=x<=10 AND x<=y)?
;   We assert the hypotheses AND the negation of the derived bound (y <= 9).
; EXPECTED: sat  => the derived bound is NOT implied => the narrowing is UNSOUND.
;   A 'sat' model (e.g. x=0, y=0) is a real solution of the assumptions that the
;   reasoner's narrowed domain y>=10 wrongly excludes. Excluding it can make a VC
;   spuriously UNSAT (false PASS).
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 0 x))
(assert (<= x 10))
(assert (<= x y))
; negation of the reasoner's derived bound y >= 10
(assert (< y 10))
(check-sat)
(get-model)
