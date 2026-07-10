; rule slug: eq-expand-K-soundness
; pass: flatten_outer_array  (walk_equals, lines 259-283)
; contract: unsat-preserving  (the soundness-critical rule)
; Background:
;   An extensional outer-array equality (= A B) (equal at EVERY Int index) is
;   rewritten to a conjunction over only the OBSERVED constant indices K:
;     (and (= (select A k) (select B k))  for k in K).
;   The rewritten form is WEAKER (constrains fewer indices). For a verifier
;   checking UNSAT (unsat = proven), the dangerous direction is turning a
;   SAT (counterexample) into UNSAT (false PASS). That cannot happen if the
;   rewrite is a RELAXATION: original |= rewritten, hence original SAT =>
;   rewritten SAT.
; What is checked (K = {1,2}):
;   (= A B)  ==>  (and (= (select A 1)(select B 1)) (= (select A 2)(select B 2)))
; EXPECTED: unsat  (sound: equal arrays are equal at 1 and 2, so the rewrite
;   only relaxes; no SAT can become UNSAT -> no false PASS).
;   A 'sat' model would mean two equal arrays disagreeing at index 1 or 2,
;   which is impossible; sat here would signal a broken expansion.
; NOTE: the CONVERSE (rewritten ==> original) is deliberately NOT valid --
;   see eq-expand-K-not-equivalence.smt2. Completeness relies on the pass's
;   enforced precondition that A,B are only ever accessed at indices in K
;   (variable-index or non-array-position uses are made ineligible and, if any
;   2D array survives, the pass raises AssertionError -- fail-closed).
; Field-agnostic: pure array theory.
(set-logic ALL)
(declare-sort X 0)
(declare-const A (Array Int (Array Int X)))
(declare-const B (Array Int (Array Int X)))
(assert (= A B))
(assert (not (and (= (select A 1) (select B 1))
                  (= (select A 2) (select B 2)))))
(check-sat)
