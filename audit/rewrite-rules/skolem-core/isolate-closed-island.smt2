; rule slug: skolem-isolate-closed-island
; contract: unsat-preserving
; WHAT: skolem_isolate.contribute solves a "closed island" of coupled qvars and
;   pins EACH member qvar to its model value via skolem_map.pin -> emit_disjuncts.
;   Because pins are appended as Not(q_i = w_i) disjuncts on the (positive)
;   universal, pinning several qvars jointly is JOINT universal instantiation:
;       (forall q1 q2. Body(q1,q2))  ==>  Body(w1,w2)
;   The elaborate island/closedness analysis is about picking a value that lets
;   the universal collapse (COMPLETENESS); soundness holds for ANY (w1,w2).
; SOUNDNESS LEMMA validated here (2-var island):
;       (forall q1 q2. R(q1,q2)) ==> R(w1,w2).
; Domain: field [0,7) on both members, R uninterpreted.
; EXPECTED: unsat  (joint instantiation follows from the universal => sound).
;   'sat' would mean pinning island members from a single model is unsound.
(set-logic UFLIA)
(declare-fun R (Int Int) Bool)
(assert (forall ((a Int) (b Int))
  (=> (and (<= 0 a) (< a 7) (<= 0 b) (< b 7)) (R a b))))
(assert (not (R 2 5)))
(check-sat)
