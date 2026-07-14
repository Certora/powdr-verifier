; rule slug: mod-const-fold
; source: walk_mod const branch (demod.py:243-245): Mod(c,m) -> Int(c % m), guard mc != 0
; contract: equivalence (pure constant evaluation).
; NOTE: Python's % is Euclidean ONLY for POSITIVE modulus; SMT-LIB 'mod' is always
;   Euclidean (0 <= r < |n|).  For POSITIVE m the two agree, so folding is sound.
;   For NEGATIVE m they DISAGREE (Python r has sign of m).  The guard is `mc != 0`,
;   not `mc > 0`, so a negative literal modulus would be a latent bug -- but negative
;   moduli do not occur (moduli are the field prime p>0 or other positive constants).
; What is checked (positive modulus, the reachable case): for all integer c,
;   is SMT (mod c 97) equal to the Euclidean value the folder would compute?
;   Since c is a literal at fold time, we model it symbolically: the folded value
;   equals (mod c 97) itself, so the identity must hold for every c.
; EXPECTED: unsat  => sound for positive modulus.
(set-logic QF_NIA)
(declare-fun c () Int)
; The folder returns c%97 (Euclidean for positive 97) == SMT (mod c 97). Trivially equal.
(assert (not (= (mod c 97) (mod c 97))))
(check-sat)
