; rule slug: pin-weakening-generic
; pass: skolem-aux
; contract: unsat-preserving (soundness of ALL skolem-aux pin contributors)
;
; WHAT IS BEING CHECKED
; ---------------------
; Every contributor in skolem_names.py / skolem_derived.py / skolem_witness.py
; only ever calls SkolemMap.pin(q, w). skolem.py::walk_forall materializes each
; pin as an extra disjunct appended to the (post-NNF, positive-polarity) forall
; body:   forall q. body(q)   ==>   forall q. ( body(q)  OR  q != w ).
; The witness w is arbitrary (it may be the "wrong" value); soundness must not
; depend on w being a correct witness.
;
; This validator proves the underlying tautology for an UNINTERPRETED body and
; an arbitrary witness w:  (forall q. body(q))  ==>  (forall q. body(q) OR q!=w).
; If that implication is valid, the whole asserted VC can only get WEAKER (more
; models), hence  Phi UNSAT  =>  Phi' UNSAT is false-direction; the sound
; direction  Phi SAT => Phi' SAT holds, so the transform never turns a real
; counterexample (SAT) into a false PASS (UNSAT).
;
; EXPECTED: unsat  (=> implication is valid => pin mechanism is sound/weakening).
; A 'sat' model would exhibit a body and witness where adding the disjunct
; STRENGTHENED the formula -- i.e. an unsound pin. None can exist.

(set-logic UFLIA)
(declare-fun body (Int) Bool)
(declare-fun w () Int)

; negation of:  (forall q. body q) => (forall q. body q or q != w)
(assert (forall ((q Int)) (body q)))
(assert (not (forall ((q Int)) (or (body q) (not (= q w))))))
(check-sat)
