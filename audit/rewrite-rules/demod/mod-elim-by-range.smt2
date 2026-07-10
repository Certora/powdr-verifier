; rule slug: mod-elim-by-range
; source: walk_mod symbol branch (demod.py:262-267), guard interval.within_0_p(m)
;   Mod(x, m) --> x   WHEN learned interval for x satisfies 0 <= lo and hi < m.
; contract: equisat / equivalence-under-context.  The range facts are top-level
;   conjuncts of the VC, so they hold in every model; in each such model
;   0 <= x < m, hence (mod x m) = x (Euclidean).
; What is checked: with the guard's exact condition (0 <= x < m) assumed,
;   is (mod x m) = x for all x?  (m=97)
; EXPECTED: unsat  => sound given the guard.  A 'sat' model would mean within_0_p
;   is not sufficient to drop the mod (bug).
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (and (<= 0 x) (< x 97)))     ; interval.within_0_p(97): lo>=0, hi<97
(assert (not (= (mod x 97) x)))
(check-sat)
