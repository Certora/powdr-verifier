; rule: mod_zero_unique  (_refine_from_mod_zero / _unique_multiple_in_domain, reasoner.py:508-513)
; contract: sound narrowing. (mod inner p)==0 and inner's domain contains a UNIQUE multiple
;   of p => inner == that multiple.
; INSTANCE: p=7, inner in [3,9]. Only multiple of 7 in [3,9] is 7 => inner == 7.
; CHECK: is (inner = 7) implied by (3<=inner<=9 and (mod inner 7)=0)?
; EXPECTED: unsat => sound.
(set-logic QF_NIA)
(declare-const inner Int)
(assert (<= 3 inner))
(assert (<= inner 9))
(assert (= (mod inner 7) 0))
(assert (not (= inner 7)))
(check-sat)
