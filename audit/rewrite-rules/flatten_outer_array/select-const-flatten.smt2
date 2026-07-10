; rule slug: select-const-flatten
; pass: flatten_outer_array  (walk_array_select, lines 250-257)
; contract: equisat (definitional variable introduction)
; What is checked:
;   (select M k) with M an outer symbol and k a constant in K is replaced by a
;   fresh symbol M__k. This is a sound definitional elimination iff M__k is
;   forced to equal (select M k). We model the elimination and check that the
;   rewrite is a RELAXATION of the original (original |= rewritten under the
;   definition M__k := (select M k)), which is the direction that matters for a
;   verifier checking UNSAT: original SAT  =>  rewritten SAT  (no false PASS).
;
;   Concretely: some property phi(select M 1, select M 2) holds in the original.
;   In the flat world M__1, M__2 are fresh but pinned by the definition. We
;   assert the definitions and check original ==> flattened is valid.
; EXPECTED: unsat  (sound: the flattened form is implied, so no counterexample
;   is lost). A 'sat' model would be an assignment satisfying the original
;   accesses but violating the flattened form -> the fresh-symbol split dropped
;   a constraint (unsound: manufactured PASS).
; Field-agnostic: pure array theory.
(set-logic QF_AUFLIA)
(declare-const M (Array Int Int))
(declare-const M__1 Int)
(declare-const M__2 Int)
; definitional pinning that the pass relies on (M__k stands for (select M k))
(assert (= M__1 (select M 1)))
(assert (= M__2 (select M 2)))
; original constraints over the concrete accesses
(declare-fun phi (Int Int) Bool)
(assert (phi (select M 1) (select M 2)))
; flattened must be implied: phi(M__1, M__2)
(assert (not (phi M__1 M__2)))
(check-sat)
