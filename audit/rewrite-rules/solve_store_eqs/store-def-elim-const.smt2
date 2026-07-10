; rule slug: store-def-elim (CONST kind)
; pass: solve_store_eqs
; contract: equisat (definitional variable elimination)
;   Same rule as store kind but E is a constant-array  ((as const (Array Int (Array Int Int))) c).
;   Substitute arr := E, fold (= E E) -> True, drop decl.
;
; WHAT IS CHECKED: under (= arr E), phi(arr) equivalent to phi(E). Expect UNSAT.
; EXPECTED: unsat => sound. sat would be a Leibniz-substitutivity violation (unsound).
(set-logic ALL)

(declare-fun arr () (Array Int (Array Int Int)))
(declare-fun innerconst () (Array Int Int))
(declare-fun a1 () Int)
(declare-fun a2 () Int)
(declare-fun a3 () Int)
(declare-fun w () Int)

; E = const 2D array whose every outer cell is innerconst.
(define-fun E () (Array Int (Array Int Int))
  ((as const (Array Int (Array Int Int))) innerconst))

(assert (= arr E))

(define-fun phi_arr () Bool
  (and
    (= (select (select arr a1) a2) w)
    (= (select arr a3) (select arr a1))))

(define-fun phi_E () Bool
  (and
    (= (select (select E a1) a2) w)
    (= (select E a3) (select E a1))))

(assert (not (= phi_arr phi_E)))
(check-sat)
