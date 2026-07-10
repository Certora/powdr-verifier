; rule slug: mod_zero_unique_multiple
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_from_mod_zero (unique-multiple, lines 508-513)
;                    + helpers.py _unique_multiple_in_domain / _unique_multiple_in_interval
; contract: unsat-preserving NARROWING (in fact exact). From (mod inner P)==0, if the
;   domain hull of `inner` contains exactly ONE multiple of P, then inner equals it.
;
; Concrete instance (P=7): inner in [5,10] (== [P-2, P+3]); only multiple of 7 in
;   [5,10] is 7 => inner == 7.
;
; CHECK: is inner==7 IMPLIED by (5<=inner<=10 AND (mod inner 7)=0)?
;   Assert hypotheses AND negation (inner != 7).
; EXPECTED: unsat  => implied => SOUND.
(set-logic QF_NIA)
(declare-fun inner () Int)
(assert (<= 5 inner))
(assert (<= inner 10))
(assert (= (mod inner 7) 0))
(assert (not (= inner 7)))
(check-sat)
