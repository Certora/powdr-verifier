; rule slug: store-def-elim (STORE kind)
; pass: solve_store_eqs
; contract: equisat (definitional variable elimination / destructive equality resolution)
;   Given a top-level conjunctive equality  (= arr E)  where arr is a declared 2D-array
;   symbol, E is a (store ...) expression, and arr does NOT occur in E (occurs check),
;   the pass substitutes arr := E everywhere, folds (= E E) -> True, drops the assert,
;   and drops arr's declaration.
;   The load-bearing semantic fact is:  under the hypothesis (= arr E), replacing any
;   occurrence of arr by E preserves truth of every formula.  (The declaration drop is
;   sound because arr is a free variable existentially eliminable once its sole pinning
;   equality is internalized by substitution; E does not mention arr.)
;
; WHAT IS CHECKED: with (= arr E) assumed, an arbitrary predicate phi(arr) built from
;   arr at several positions is equivalent to phi(E) (arr textually replaced by E).
;   Assert (= arr E) and (not (= phi_arr phi_E)); expect UNSAT.
;
; EXPECTED: unsat  => sound (substitution under the equality preserves truth).
;   A 'sat' model would exhibit an arr and E with arr=E for which some phi(arr) differs
;   from phi(E) -- impossible under Leibniz substitutivity; would signal an encoding of a
;   rewrite that reads arr in a context the equality does not actually govern (unsound).
;
; Field prime P is irrelevant to this pass (no modular arithmetic); arrays are abstract.
(set-logic ALL)

; 2D array: (Array Int (Array Int Int))
(declare-fun arr  () (Array Int (Array Int Int)))
(declare-fun base () (Array Int (Array Int Int)))
(declare-fun inner () (Array Int Int))
(declare-fun k () Int)
(declare-fun a1 () Int)
(declare-fun a2 () Int)
(declare-fun a3 () Int)
(declare-fun w () Int)

; E = (store base k inner)  -- a store RHS not mentioning arr
(define-fun E () (Array Int (Array Int Int)) (store base k inner))

; The pinning top-level conjunctive equality.
(assert (= arr E))

; phi(arr): arr used at multiple positions (outer select, nested select, store, eq).
(define-fun phi_arr () Bool
  (and
    (= (select (select arr a1) a2) w)
    (= (select arr a3) (select arr k))
    (= (store arr a1 inner) (store arr a3 inner))))

; phi(E): the same predicate with arr textually replaced by E (what the pass emits).
(define-fun phi_E () Bool
  (and
    (= (select (select E a1) a2) w)
    (= (select E a3) (select E k))
    (= (store E a1 inner) (store E a3 inner))))

(assert (not (= phi_arr phi_E)))
(check-sat)
