; rule slug: pin-weakening-finite
; pass: skolem-aux
; contract: unsat-preserving (decidable companion to pin-weakening-generic)
;
; WHAT IS BEING CHECKED
; ---------------------
; Fully quantifier-free, decidable instantiation of the pin-weakening theorem.
; Domain of the qvar q is the 3-element set {0,1,2}; body(q) is modelled by three
; free booleans B0,B1,B2; A is an unrelated top-level conjunct. We pin q := w
; with a DELIBERATELY ARBITRARY witness w (could be out of domain).
;
;   original  Phi  = A and (B0 and B1 and B2)            [forall q in {0,1,2}. body q]
;   modified  Phi' = A and AND_{q in {0,1,2}} (body q OR q != w)
;
; Check original => modified is VALID (negation unsat). This shows the appended
; disjunct can only weaken, for every choice of w including w outside {0,1,2}.
;
; EXPECTED: unsat (implication valid => sound weakening).
; A 'sat' model would be a witness w for which the pinned formula excludes a
; model of the original -- an unsound strengthening. None exists.

(set-logic QF_LIA)
(declare-fun A () Bool)
(declare-fun B0 () Bool)
(declare-fun B1 () Bool)
(declare-fun B2 () Bool)
(declare-fun w () Int)

(define-fun orig () Bool (and A B0 B1 B2))
(define-fun bodyq ((q Int) (bq Bool)) Bool (or bq (not (= q w))))
(define-fun modified () Bool
  (and A (bodyq 0 B0) (bodyq 1 B1) (bodyq 2 B2)))

; negation of (orig => modified)
(assert orig)
(assert (not modified))
(check-sat)
