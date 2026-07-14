; rule slug: alias_to_forward
; pass: define_inner_array   (_build_body, symbol/alias branch + _read)
; contract: equisat / equivalence (definitional extension)
; transform: arr uniquely defined by (assert (= arr other)) is dropped and replaced
;   by macro arr__fn(i) = other_read(i); (select arr j) -> (arr__fn j).
; WHAT IS CHECKED: given arr = other, does (select arr i) == (select other i)?
; EXPECTED: unsat (sound). sat would mean the alias macro reads a different value
;   than the aliased array -> unsound.
(set-logic QF_ALIA)
(declare-fun other () (Array Int Int))
(declare-fun i () Int)
(define-fun arr () (Array Int Int) other)
(assert (not (= (select arr i) (select other i))))
(check-sat)
