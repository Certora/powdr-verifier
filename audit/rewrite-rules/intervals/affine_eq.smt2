; rule slug: affine_eq
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_affine_eq (lines 237-287)
; contract: unsat-preserving NARROWING (two-sided; equality gives an interval).
;   From  const + sum(terms) == 0, isolate sym: coeff*sym = -other, other in [h.lo,h.hi]
;   => sym in [ceil(-h.hi/coeff), floor(-h.lo/coeff)] (coeff>0). Both endpoints used,
;   which is correct because equality is two-sided.
;
; Concrete instance:  x + y == 5, assumed 0 <= y <= 3.
;   other for x = -5 + dom(y) = [-5,-2]; coeff=1 => x in [2,5].
;
; CHECK: is  2 <= x <= 5  IMPLIED by (x+y=5 AND 0<=y<=3)?
;   Assert hypotheses AND negation NOT(2<=x AND x<=5).
; EXPECTED: unsat  => bound implied => SOUND.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 5))
(assert (<= 0 y))
(assert (<= y 3))
(assert (not (and (<= 2 x) (<= x 5))))
(check-sat)
