; rule slug: eq-expand-K-not-equivalence  (companion / negative control)
; pass: flatten_outer_array  (walk_equals, lines 259-283)
; contract: documents that eq-expand is NOT a full equivalence, only a
;   one-directional relaxation. Soundness (no false PASS) rests on the
;   relaxation direction (see eq-expand-K-soundness.smt2); COMPLETENESS rests
;   on the pass's precondition that A,B are accessed only at K.
; What is checked (K = {1,2}):
;   Does the rewritten form imply the original extensional equality?
;     (and (= (select A 1)(select B 1)) (= (select A 2)(select B 2)))
;        ==>  (= A B)
; EXPECTED: sat  (NOT a bug). The model has A,B equal at indices 1,2 but
;   differing at some other index -> the K-restricted conjunction holds while
;   the extensional equality fails. This is exactly why the pass MUST enforce
;   "arrays accessed only at K": if any access outside K existed, this gap
;   would be a real completeness loss (rewritten SAT while original UNSAT =
;   false FAIL). It is never a false PASS, so it is not a soundness hole.
; Field-agnostic: pure array theory.
(set-logic ALL)
(declare-sort X 0)
(declare-const A (Array Int (Array Int X)))
(declare-const B (Array Int (Array Int X)))
(assert (and (= (select A 1) (select B 1))
             (= (select A 2) (select B 2))))
(assert (not (= A B)))
(check-sat)
