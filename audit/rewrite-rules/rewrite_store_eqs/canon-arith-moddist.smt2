; rule: canon-arith mod-distribution   (_canon_arith lines 69-93), used as the index-equality
;   test at _reduce line 149.  Claim: under an OUTER (mod _ p), inner (mod _ p) wrappers on
;   Plus/Times operands may be stripped (distributive law), and operands reordered.
; soundness question: does canon ever equate two indices that are NOT integer-equal?
;   If canon(i1) == canon(i2) syntactically and canon is value-preserving, then i1,i2 are
;   integer-equal, so applying the SAME-index store rule is justified.
; CHECK the keccak example equality holds as EXACT integers (small p = 97):
;   (mod ((x*65536)+y) p) == (mod ((65536*(x mod p)) + (y mod p)) p)   for all x,y
; assert its negation.  EXPECTED: unsat  (unsat = canon is value-preserving here = sound test)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (mod (+ (* x 65536) y) 97)
                (mod (+ (* 65536 (mod x 97)) (mod y 97)) 97))))
(check-sat)
