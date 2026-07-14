; rule slug: skolem-rules-diff_val-witness
; contract: unsat-preserving as an append (SOUND for any witness); this file
;   validates WITNESS CORRECTNESS (a completeness property, and a sanity check
;   that _build_skolem encodes the intended OpenVM value).
; pass: skolem-core (src/simplify/skolem_rules.py:_build_skolem / _build_marker_skolems)
;
; WHAT IS CHECKED:
;   The canonical diff_val witness (nested Ite from _build_skolem) together with
;   the marker witnesses (_build_marker_skolems) must satisfy OpenVM's
;   DiffMarkerConstraints constr_5..8 for the constant c=(1,0,0,0) (LSB-first):
;       diff_marker_i * (a_i_e * sign + diff_val) == 0   (mod P)
;   where a_0_e = b0 - 1 (c0=1), a_i_e = b_i (c_i=0), sign = 2*cmp - 1.
;   diff_val = -b_{i*} * sign at the highest limb i* with b differing from c,
;   marker_{i*}=1 there and 0 elsewhere. Small prime P=7, cmp in {0,1},
;   b0..b3 in the field.
; EXPECTED: unsat  (the witness satisfies every DiffMarkerConstraint => the
;   intended value; corroborates the rule).  A 'sat' model would exhibit
;   b,cmp where the built witness violates a constraint = a witness/formula bug
;   (a COMPLETENESS defect: the pin would fail to collapse the universal), not a
;   soundness hole (the append is sound regardless).
(set-logic QF_NIA)
(declare-fun b0 () Int)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun b3 () Int)
(declare-fun cmp () Int)
(assert (and (<= 0 b0) (< b0 7) (<= 0 b1) (< b1 7)
             (<= 0 b2) (< b2 7) (<= 0 b3) (< b3 7)))
(assert (or (= cmp 0) (= cmp 1)))            ; boolean flag

(define-fun sign () Int (+ 6 (* 2 cmp)))     ; 2*cmp - 1  == 6 + 2*cmp (mod 7)

; diff_val = nested Ite, MSB-first, c=(1,0,0,0)
(define-fun row0 () Int (ite (= b0 1) 0 (* (+ 1 (* 6 b0)) sign)))
(define-fun e1 () Int (ite (= b1 0) row0 (* (* 6 b1) sign)))
(define-fun e2 () Int (ite (= b2 0) e1 (* (* 6 b2) sign)))
(define-fun e3 () Int (ite (= b3 0) e2 (* (* 6 b3) sign)))
(define-fun diff_val () Int (mod e3 7))

; marker witnesses
(define-fun dm3 () Int (ite (= b3 0) 0 1))
(define-fun dm2 () Int (ite (= b3 0) (ite (= b2 0) 0 1) 0))
(define-fun dm1 () Int (ite (= b3 0) (ite (= b2 0) (ite (= b1 0) 0 1) 0) 0))
(define-fun dm0 () Int (ite (= b3 0) (ite (= b2 0) (ite (= b1 0) (ite (= b0 1) 0 1) 0) 0) 0))

; a_i_e limb-offset terms
(define-fun a0e () Int (- b0 1))
(define-fun a1e () Int b1)
(define-fun a2e () Int b2)
(define-fun a3e () Int b3)

; constr_5..8 (mod 7); look for any violation
(define-fun c5 () Int (mod (* dm0 (+ (* a0e sign) diff_val)) 7))
(define-fun c6 () Int (mod (* dm1 (+ (* a1e sign) diff_val)) 7))
(define-fun c7 () Int (mod (* dm2 (+ (* a2e sign) diff_val)) 7))
(define-fun c8 () Int (mod (* dm3 (+ (* a3e sign) diff_val)) 7))
(assert (or (not (= c5 0)) (not (= c6 0)) (not (= c7 0)) (not (= c8 0))))
(check-sat)
