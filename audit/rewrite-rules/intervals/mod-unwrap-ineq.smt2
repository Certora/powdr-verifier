; rule: mod_unwrap  (_refine_from_ineq / simplify, unwrap (mod e p) -> e when e in [0,p))
; contract: equivalence, guarded by e in [0,p). Euclidean mod: 0<=e<p => (mod e p) = e.
; INSTANCE: p=7, e in [0,7).
; CHECK: is (mod e 7) = e implied by (0 <= e and e < 7)?
; EXPECTED: unsat => sound.
(set-logic QF_NIA)
(declare-const e Int)
(assert (<= 0 e))
(assert (< e 7))
(assert (not (= (mod e 7) e)))
(check-sat)
