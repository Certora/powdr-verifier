; rule: store-read (define-fun body from store + select->call rewrite)
; contract: equivalence (McCarthy select-over-store axiom)
; check: arr = (store base idx val); arr__fn(i) = ite(i=idx, val, select(base,i)).
;        Assert (select (store base idx val) j) != arr__fn(j).
; EXPECTED: unsat  (sound). A sat model would be a j where the macro
;           disagrees with the real select -> unsound body construction.
(set-logic ALL)
(declare-const base (Array Int Int))
(declare-const idx Int)
(declare-const val Int)
(declare-const j Int)
(define-fun arrfn ((i Int)) Int (ite (= i idx) val (select base i)))
(assert (not (= (select (store base idx val) j) (arrfn j))))
(check-sat)
