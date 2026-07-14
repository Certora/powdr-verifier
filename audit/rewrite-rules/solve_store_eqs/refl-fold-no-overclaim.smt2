; rule slug: refl-fold negative control (NOT a transform the pass performs)
; pass: solve_store_eqs
; contract: n/a -- guards that _FoldRefl only collapses SYNTACTICALLY identical (= e e).
;   The walker's walk_equals returns True only when args[0] == args[1] (same hash-consed
;   FNode). It never tries to prove two DIFFERENT store expressions equal. This file is a
;   negative control: two distinct store expressions S and S2 are NOT semantically forced
;   equal, so a hypothetical over-eager fold that collapsed (= S S2) -> True would be
;   unsound. We confirm z3 can make them differ.
;
; WHAT IS CHECKED: (distinct-content) two stores over different bases can disagree.
;   Assert (not (= S S2)) is satisfiable.
; EXPECTED: sat  => confirms distinct stores are genuinely distinguishable; the pass is
;   sound precisely because it does NOT collapse them (only syntactic identity folds).
(set-logic ALL)

(declare-fun base  () (Array Int (Array Int Int)))
(declare-fun base2 () (Array Int (Array Int Int)))
(declare-fun inner () (Array Int Int))
(declare-fun k () Int)

(define-fun S  () (Array Int (Array Int Int)) (store base  k inner))
(define-fun S2 () (Array Int (Array Int Int)) (store base2 k inner))

(assert (not (= S S2)))
(check-sat)
