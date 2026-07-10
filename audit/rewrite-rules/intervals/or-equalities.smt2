; rule: or_equalities  (_refine_from_or_equalities, reasoner.py:457-482)
; contract: equivalence. OR of (sym==c_i) over one sym  <=>  sym in {c_i}.
; INSTANCE: (x=1 or x=4)  <=>  x in {1,4}.
; CHECK: does the disjunction differ from the recorded domain {1,4}?
; EXPECTED: unsat => sound (the two are logically equivalent; xor is unsatisfiable).
(set-logic QF_LIA)
(declare-const x Int)
(assert (xor (or (= x 1) (= x 4)) (or (= x 1) (= x 4))))
(check-sat)
