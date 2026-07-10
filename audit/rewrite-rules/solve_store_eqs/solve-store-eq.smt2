; rule slug: solve-store-eq
; pass: solve_store_eqs
; contract: equisat  (definitional variable elimination)
;
; RULE: Given a top-level conjunctive equality (= arr E) where
;   - arr is a declared 2D-array free symbol (value type is itself an array),
;   - E is a (store ...) expression,
;   - arr does NOT occur free in E (occurs-check at solve_store_eqs.py:82),
; substitute arr := E across ALL asserts, then drop the equality (it folds to
; (= E E) -> True) and drop arr's declaration.
;
; Direction that matters for the verifier: unsat-preserving (original UNSAT =>
; rewritten UNSAT). equisat gives both directions, so it suffices to validate
; that uniform substitution preserves the truth value of every constraint under
; the pinning equality arr = E.
;
; WHAT IS CHECKED (validity form of soundness of uniform substitution):
;   Under the definitional pin (assert (= arr E)), the constraint body evaluated
;   on `arr` must have the SAME truth value as the body with arr replaced by E.
;   If they can differ, substitution is unsound.
;     pin:   arr = E
;     goal:  NOT ( C(arr) <=> C(E) )   -> expect UNSAT
;
; EXPECTED VERDICT: unsat  => rule is SOUND.
;   A 'sat' model would exhibit an assignment where the pinned equality holds yet
;   substituting arr:=E changes the meaning of some constraint (unsound).
;
; No field arithmetic is involved in this pass, so no prime is needed; arrays are
; over Int index / Int value with a nested (2D) value type.

(set-logic ALL)

; 2D array type: outer index Int -> (inner array Int -> Int)
(declare-fun arr    () (Array Int (Array Int Int)))   ; the symbol to eliminate
(declare-fun base   () (Array Int (Array Int Int)))   ; occurs in E
(declare-fun inner  () (Array Int Int))               ; occurs in E
(declare-fun i0 () Int)
(declare-fun j0 () Int)
(declare-fun k  () Int)
(declare-fun m  () Int)
(declare-fun v0 () Int)
(declare-fun P  () Bool)

; E = (store base i0 inner)  -- a store term whose free vars do NOT include arr
(define-fun E () (Array Int (Array Int Int)) (store base i0 inner))

; C(x): a constraint body that uses the 2D array x both positively and inside a
; negated equality within an (or ...) -- exactly the docstring's motivating shape.
(define-fun Cx ((x (Array Int (Array Int Int)))) Bool
  (and
    (= (select (select x k) m) v0)
    (or P (not (= x E)))
    (= (select x i0) inner)))

; Definitional pin: the top-level conjunctive equality.
(assert (= arr E))

; Soundness of uniform substitution: body(arr) must agree with body(E).
(assert (not (= (Cx arr) (Cx E))))

(check-sat)
