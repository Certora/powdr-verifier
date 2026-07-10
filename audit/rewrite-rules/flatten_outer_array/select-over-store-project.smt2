; rule slug: select-over-store-project
; pass: flatten_outer_array  (_project ARRAY_STORE branch, lines 231-237)
; contract: equivalence
; What is checked:
;   _project((store base i v), k) for CONSTANT i,k returns
;     v            if i == k
;     _project(base,k)  otherwise
;   This is exactly the McCarthy select-over-store axiom specialized to the
;   constant-index case the code actually takes. We check the standard axiom:
;     (select (store base i v) k) == (ite (= i k) v (select base k))
; EXPECTED: unsat  (rule is sound / equivalence holds).
;   A 'sat' model would exhibit array indices i,k and a base/v where the
;   flattened projection disagrees with the true select-over-store value,
;   i.e. the store-flattening in _project is wrong.
; Field-agnostic: pure array theory, no BabyBear arithmetic involved.
(set-logic ALL)
(declare-sort X 0)
(declare-const base (Array Int X))
(declare-const i Int)
(declare-const k Int)
(declare-const v X)
(assert (not
  (= (select (store base i v) k)
     (ite (= i k) v (select base k)))))
(check-sat)
