; rule slug: solve-const-array-eq
; pass: solve_store_eqs
; contract: equisat  (definitional variable elimination)
;
; RULE: same as solve-store-eq but the RHS E is a constant-array term
;   ((as const (Array Int (Array Int Int))) ci)   [node type ARRAY_VALUE].
; Given a top-level conjunctive (= arr E) with arr a declared 2D-array free
; symbol and arr not free in E, substitute arr := E everywhere, drop the eq,
; drop the decl.
;
; Direction that matters: unsat-preserving; equisat gives both. Validated via the
; uniform-substitution validity check:
;     pin:   arr = E
;     goal:  NOT ( C(arr) <=> C(E) )   -> expect UNSAT
;
; EXPECTED VERDICT: unsat => SOUND.
;   'sat' would mean the pin holds but substitution changes a constraint's value.

(set-logic ALL)

(declare-fun arr () (Array Int (Array Int Int)))
(declare-fun ci  () (Array Int Int))     ; the constant inner array filling E
(declare-fun k () Int)
(declare-fun m () Int)
(declare-fun v0 () Int)
(declare-fun P () Bool)

; E = a 2D constant array: every outer index maps to the inner array `ci`.
(define-fun E () (Array Int (Array Int Int))
  ((as const (Array Int (Array Int Int))) ci))

(define-fun Cx ((x (Array Int (Array Int Int)))) Bool
  (and
    (= (select (select x k) m) v0)
    (or P (not (= x E)))))

(assert (= arr E))
(assert (not (= (Cx arr) (Cx E))))

(check-sat)
