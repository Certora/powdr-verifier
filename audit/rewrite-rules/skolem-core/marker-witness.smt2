; rule slug: skolem-rules-marker-witness
; contract: unsat-preserving as an append (SOUND for any witness); this file
;   validates WITNESS CORRECTNESS of _build_marker_skolems (completeness sanity).
; pass: skolem-core (src/simplify/skolem_rules.py:_build_marker_skolems)
;
; WHAT IS CHECKED:
;   The marker witnesses must satisfy the remaining OpenVM LessThan constraints
;   for c=(1,0,0,0), beyond constr_5..8 (checked in diff_val-witness.smt2):
;     constr_9 : sum_dm * (sum_dm - 1) == 0        (sum of markers is a flag)
;     constr_0..2 (i=1,2,3): (1 - sum_{j>=i} dm_j) * a_i_e * sign == 0  (mod 7)
;     constr_4 : (1 - sum_dm) * a_0_e * sign == 0   (mod 7)
;   with a_0_e=b0-1, a_i_e=b_i, sign=2*cmp-1. These force markers to select the
;   highest limb differing from c and to be all-zero iff b==c. P=7.
; EXPECTED: unsat  (markers satisfy all constraints => correct witness).
;   A 'sat' model would be a b,cmp where the marker witness violates a constraint
;   = a completeness defect in _build_marker_skolems (not a soundness hole).
(set-logic QF_NIA)
(declare-fun b0 () Int)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun b3 () Int)
(declare-fun cmp () Int)
(assert (and (<= 0 b0) (< b0 7) (<= 0 b1) (< b1 7)
             (<= 0 b2) (< b2 7) (<= 0 b3) (< b3 7)))
(assert (or (= cmp 0) (= cmp 1)))
(define-fun sign () Int (+ 6 (* 2 cmp)))

(define-fun dm3 () Int (ite (= b3 0) 0 1))
(define-fun dm2 () Int (ite (= b3 0) (ite (= b2 0) 0 1) 0))
(define-fun dm1 () Int (ite (= b3 0) (ite (= b2 0) (ite (= b1 0) 0 1) 0) 0))
(define-fun dm0 () Int (ite (= b3 0) (ite (= b2 0) (ite (= b1 0) (ite (= b0 1) 0 1) 0) 0) 0))

(define-fun sum_dm () Int (+ dm0 dm1 dm2 dm3))
(define-fun a0e () Int (- b0 1))

; constr_9: sum_dm in {0,1}
(define-fun c9 () Int (* sum_dm (- sum_dm 1)))
; constr_0..2: (1 - sum_{j>=i} dm) * a_i * sign, i=1,2,3
(define-fun c0 () Int (mod (* (- 1 (+ dm1 dm2 dm3)) (* b1 sign)) 7))
(define-fun c1 () Int (mod (* (- 1 (+ dm2 dm3)) (* b2 sign)) 7))
(define-fun c2 () Int (mod (* (- 1 dm3) (* b3 sign)) 7))
; constr_4: (1 - sum_dm) * (a0 - 1) * sign
(define-fun c4 () Int (mod (* (- 1 sum_dm) (* a0e sign)) 7))

(assert (or (not (= c9 0)) (not (= c0 0)) (not (= c1 0))
            (not (= c2 0)) (not (= c4 0))))
(check-sat)
