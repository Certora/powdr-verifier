; rule slug: top-eq-elim-both-symbols
; pass: solve_eqs  (_pick_elim_target, "both sides declared symbols" branch)
; contract: EQUISAT (tie-break heuristic: eliminate the later-declared symbol)
;
; RULE: for (= a b) with BOTH a,b declared eligible symbols, the pass eliminates
;   whichever was declared later, substituting it with the earlier one. The claim
;   under audit is only that the CHOICE of which symbol to eliminate does not
;   affect satisfiability -- both orientations of the one-point rule are sound.
;
; We check the two orientations are equisat to each other (and to the pre-elim
;   existential closure): eliminating x (x:=y) vs eliminating y (y:=x) yield
;   equisat results.
;       (exists x y. (x=y /\ R(x,y)))  <=>  (exists y. R(y,y))  [x:=y]
;                                       <=>  (exists x. R(x,x))  [y:=x]
;
; EXPECTED: unsat => both orientations equivalent => tie-break is SOUND.
;   'sat' would mean the arbitrary choice of elimination target changes meaning.
(set-logic ALL)
(declare-fun c () Int)
(define-fun P () Int 97)
; R(x,y): a symmetric-ish context mentioning both.
(define-fun R ((x Int) (y Int)) Bool
  (and (= (mod (+ x y c) P) 0) (<= 0 x) (< x P) (<= 0 y) (< y P)))
(assert (and (<= 0 c) (< c P)))
(define-fun elim_x () Bool (exists ((y Int)) (R y y)))   ; x:=y
(define-fun elim_y () Bool (exists ((x Int)) (R x x)))   ; y:=x
(define-fun pre () Bool (exists ((x Int) (y Int)) (and (= x y) (R x y))))
(assert (not (and (= pre elim_x) (= pre elim_y))))
(check-sat)
