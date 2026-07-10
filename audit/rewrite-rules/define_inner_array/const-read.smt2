; rule: const-read (define-fun body from constant array)
; contract: equivalence
; check: arr = ((as const (Array Int Int)) d); arr__fn(i) = d.
;        Assert (select const_array j) != arr__fn(j).
; EXPECTED: unsat (sound). sat = macro disagrees with const-array read.
(set-logic ALL)
(declare-const d Int)
(declare-const j Int)
(define-fun arrfn ((i Int)) Int d)
(assert (not (= (select ((as const (Array Int Int)) d) j) (arrfn j))))
(check-sat)
