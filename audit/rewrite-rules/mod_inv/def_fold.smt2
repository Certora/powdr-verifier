; rule slug : def_fold  (mod_inv definition-level folding)
; contract  : unsat-preserving  (rewrite must be a relaxation of the intended
;             field semantics; direction that matters: intended-SAT => rewritten-SAT)
; what      : Original definition (uf_mod_inv interpreted as the true field inverse):
;                 V = ( ite (T==0 mod P) 0  (C * inv(T)) )  mod P
;             is rewritten to the two implications:
;                 (mod T P)=0  =>  V=0
;                 (mod T P)!=0 =>  (mod (T*V) P) = (mod C P)
;             We look for a model of the INTENDED semantics (A*) that VIOLATES the
;             rewrite (B).  If none exists, the rewrite never kills a genuine model.
; expected  : unsat  => SOUND (B is implied by A*, cannot manufacture a false PASS).
;             sat    => UNSOUND: the (T,C,V) model is permitted by the true inverse
;                       semantics but ruled out by the rewritten constraints.
(set-logic QF_NIA)
(define-fun P () Int 7)
(declare-fun T () Int)
(declare-fun C () Int)
(declare-fun V () Int)
(declare-fun I () Int)   ; genuine field inverse of T when T != 0

; field-element domain (canonically reduced representatives)
(assert (and (<= 0 T) (< T P)))
(assert (and (<= 0 C) (< C P)))
(assert (and (<= 0 V) (< V P)))
(assert (and (<= 0 I) (< I P)))

; A* : I is the true inverse of T for T != 0
(assert (=> (not (= (mod T P) 0)) (= (mod (* I T) P) 1)))
; A* : the QuotientOrZero definition
(assert (=> (= (mod T P) 0) (= V 0)))
(assert (=> (not (= (mod T P) 0)) (= V (mod (* C I) P))))

; ¬B : negation of the rewrite
(assert (not (and
   (=> (= (mod T P) 0)       (= V 0))
   (=> (not (= (mod T P) 0)) (= (mod (* T V) P) (mod C P))))))

(check-sat)
