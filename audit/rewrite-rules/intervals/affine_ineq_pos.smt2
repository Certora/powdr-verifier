; rule slug: affine_ineq_pos
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_affine_ineq (coeff > 0 branch, lines 324-335)
; contract: unsat-preserving NARROWING.
;   For  coeff*sym + rest {<=} target_hi  with coeff>0, the code derives
;   sym <= floor((target_hi - rest.LO)/coeff).  Uses rest.LO -> matches the sound
;   existential projection (choose smallest rest to keep feasibility).
;
; Concrete instance:  constraint x <= y, assumed 0 <= y <= 10 (rest = -dom(y), h.lo=-10),
;   target_hi=0, coeff for x is +1  =>  x <= (0 - (-10))/1 = 10.
;
; CHECK: is derived bound  x <= 10  IMPLIED by (0<=y<=10 AND x<=y)?
;   Assert hypotheses AND negation (x >= 11).
; EXPECTED: unsat  => bound is implied => narrowing SOUND for this branch.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 0 y))
(assert (<= y 10))
(assert (<= x y))
(assert (> x 10))
(check-sat)
