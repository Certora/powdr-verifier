; rule slug: normalize-arith-under-mod
; source: _normalize_arith_under_mod, applied inside walk_mod (demod.py:67-89, 241-242)
; contract: equivalence of the mod value.  The transform reshapes E into E' where
;   E' is congruent to E mod m, and it is only ever placed back under Mod(., m):
;     Mod(E, m) --> Mod(E', m)
;   Rewrites:  Minus(a,b) -> a + (m-1)*b ;  int literal k -> k%m ; recurse +,*,ite.
; What is checked: for arbitrary integers, does Mod of the original expression
;   equal Mod of the normalized expression, for a representative nested E:
;     E  = ((a - b) + 5) * c
;     E' = ((a + 96*b) + 5) * c        (m=97, m-1=96, 5%97=5)
; EXPECTED: unsat  => congruence-preserving, sound equivalence.
;   A 'sat' model would be an (a,b,c) where the two mods differ (bug).
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(define-fun E  () Int (* (+ (- a b) 5) c))
(define-fun E2 () Int (* (+ (+ a (* 96 b)) 5) c))
(assert (not (= (mod E 97) (mod E2 97))))
(check-sat)
