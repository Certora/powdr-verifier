; rule: definitional-extension (drop decl of arr + drop (= arr expr), inline as macro)
; contract: equisat (definitional extension)
; check: for a concrete surrounding predicate Q, the ORIGINAL
;          (exists arr. arr = (store base idx val) /\ Q(select arr j))
;        is boolean-equivalent to the TRANSFORMED  Q(arrfn j).
;        Here Q(x) := (= x 5). arr is fully pinned by its defining eq, so the
;        existential collapses; equisat reduces to the store-read axiom.
; EXPECTED: unsat (sound). sat = the elimination changes satisfiability.
(set-logic ALL)
(declare-const base (Array Int Int))
(declare-const idx Int)
(declare-const val Int)
(declare-const j Int)
(define-fun arrfn ((i Int)) Int (ite (= i idx) val (select base i)))
(assert (not (=
  (exists ((arr (Array Int Int)))
     (and (= arr (store base idx val)) (= (select arr j) 5)))
  (= (arrfn j) 5))))
(check-sat)
