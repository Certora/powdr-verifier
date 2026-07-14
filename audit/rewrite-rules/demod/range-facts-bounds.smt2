; rule slug: range-facts-bounds
; source: extract_symbol_ranges strict/non-strict/equality/negation handling
;   (demod.py:141-185).  Each top-level relation contributes an interval bound:
;     x <  c  =>  x <= c-1        c <  x  =>  x >= c+1
;     x <= c  =>  x <= c          c <= x  =>  x >= c
;     x =  c  =>  x in [c,c]      and negated forms via _normalized_relation.
; contract: each recorded bound must be ENTAILED by the source fact (so that using
;   it downstream to drop mods is sound).  These bounds are only ever used to feed
;   mod-elim-by-range, whose facts are top-level conjuncts (hold in all models).
; What is checked: the two nontrivial (strict->closed integer) conversions.
;   For integers:  (x < c) => (x <= c-1)   and   (c < x) => (x >= c+1).
; EXPECTED: unsat for both => the integer tightening is sound.
;   A 'sat' model would be an integer x satisfying the strict fact but violating the
;   recorded closed bound (bug).
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun c () Int)
(assert (or
          (and (< x c) (not (<= x (- c 1))))    ; x<c but recorded x<=c-1 fails
          (and (< c x) (not (>= x (+ c 1))))))  ; c<x but recorded x>=c+1 fails
(check-sat)
