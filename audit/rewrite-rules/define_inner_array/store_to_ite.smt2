; rule slug: store_to_ite
; pass: define_inner_array   (_build_body, ARRAY_STORE branch)
; contract: equisat / equivalence (definitional extension)
; transform: an array `arr` uniquely defined by (assert (= arr (store base k v)))
;   is dropped and replaced by macro
;     arr__fn(i) = (ite (= i k) v (base_read i))
;   and every (select arr j) is rewritten to (arr__fn j).
; WHAT IS CHECKED: the select-over-store axiom the macro encodes.
;   Given arr = (store base k v), is (select arr i) == (ite (= i k) v (select base i))
;   for the arbitrary index i?  This is exactly what arr__fn(i) computes, so the
;   select->call rewrite is value-preserving iff this holds.
; EXPECTED: unsat  (sound). A sat model would exhibit an index where the macro
;   disagrees with the real select-over-store value -> select->call would change
;   the formula's meaning -> unsound.
(set-logic QF_ALIA)
(declare-fun base () (Array Int Int))
(declare-fun k () Int)
(declare-fun v () Int)
(declare-fun i () Int)
(define-fun arr () (Array Int Int) (store base k v))
(assert (not (= (select arr i)
                (ite (= i k) v (select base i)))))
(check-sat)
