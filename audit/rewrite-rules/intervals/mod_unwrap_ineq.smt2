; rule slug: mod_unwrap_ineq
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_from_ineq (unwrap of (mod E P) when E in [0,P), lines 388-395)
; contract: equivalence, under the guard that E's domain is canonical [0,P).
;   The reasoner replaces (mod E P) by E inside an inequality when E in [0,P),
;   because then (mod E P) == E (Euclidean).
;
; CHECK (P=7): under 0 <= E < 7, are the atoms  ((mod E 7) <= 3)  and  (E <= 3)  equivalent?
;   Assert 0<=E<7 AND the two atoms differ.
; EXPECTED: unsat  => equivalent under the guard => SOUND.
(set-logic QF_NIA)
(declare-fun E () Int)
(assert (<= 0 E))
(assert (< E 7))
(assert (distinct (<= (mod E 7) 3) (<= E 3)))
(check-sat)
