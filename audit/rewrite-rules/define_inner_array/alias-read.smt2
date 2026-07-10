; rule: alias-read (define-fun body from array-symbol alias)
; contract: equivalence
; check: arr = other; arr__fn(i) = (select other i).
;        Assert (select other j) != arr__fn(j).
; EXPECTED: unsat (sound, trivial). sat = alias body wrong.
(set-logic ALL)
(declare-const other (Array Int Int))
(declare-const j Int)
(define-fun arrfn ((i Int)) Int (select other i))
(assert (not (= (select other j) (arrfn j))))
(check-sat)
