; rule slug: project-const-array
; pass: flatten_outer_array  (_project ARRAY_VALUE branch, lines 238-241)
; contract: equivalence
; What is checked:
;   _project((as const (Array Int X)) d, k) returns the default d.
;   Semantically (select (const d) k) == d for every k.
; EXPECTED: unsat  (sound / equivalence).
;   A 'sat' model would mean projecting a constant outer array at some index
;   yields something other than its default -- impossible, so unsat confirms.
; Field-agnostic: pure array theory.
(set-logic ALL)
(declare-sort X 0)
(declare-const d X)
(declare-const k Int)
(assert (not
  (= (select ((as const (Array Int X)) d) k) d)))
(check-sat)
