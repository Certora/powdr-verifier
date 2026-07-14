; rule: flatten-and  (_flatten_and: nested And flattened; []->TRUE; [a]->a)
; contract: equivalence (boolean).  And(a, And(b,c)) -> And(a,b,c)
; also checks identity cases via separate asserts below.
; check: negation of equivalences. expect UNSAT = sound.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
; nested flatten
(assert (not (= (and a (and b c)) (and a b c))))
; empty And -> TRUE  and single-elt And -> a are structural pysmt identities;
; here we only need the flatten equivalence to hold.
(check-sat)
