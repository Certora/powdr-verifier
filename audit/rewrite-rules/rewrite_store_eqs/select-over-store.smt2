; rule: select-over-store   (walk_array_select + _read, lines 110-126, 240-255)
; (select (store a k v) k')  with constant indices:
;    k' == k  -> v
;    k' != k  -> (select a k')     (peel, recurse)
; (select (as const T d) k')    -> d
; contract: equivalence (standard select-over-store / const-array read).
; CHECK: conjunction of all three resolutions is valid; assert its negation.
; EXPECTED: unsat  (unsat = sound)
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const v Int)
(declare-const d Int)
(assert (not (and
  (= (select (store a 5 v) 5) v)                      ; equal indices -> stored value
  (= (select (store a 5 v) 7) (select a 7))           ; distinct const indices -> peel
  (= (select ((as const (Array Int Int)) d) 3) d)     ; const-array default
)))
(check-sat)
