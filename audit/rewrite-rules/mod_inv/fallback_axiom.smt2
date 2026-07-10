; rule slug : fallback_axiom  (per-term uf_mod_inv fallback)
; contract  : unsat-preserving / equisat.  Soundness hinges on P being PRIME.
; what      : Each uf_mod_inv(T) is replaced by fresh I with the added constraint
;                 (mod T P)!=0  =>  (mod (I*T) P) = 1
;             Adding a constraint can only be sound if it is always SATISFIABLE for
;             the intended semantics, i.e. every nonzero field element has an inverse.
;             This search looks for a nonzero T with NO inverse in [0,P).
; expected  : unsat  => every nonzero T is invertible (prime field) => SOUND
;                       (the added axiom is always satisfiable, never fabricates UNSAT).
;             sat    => a nonzero T with no inverse => the fallback axiom is UNSAT for
;                       a value the uninterpreted original allowed => false PASS.
(set-logic NIA)
(define-fun P () Int 7)             ; small PRIME
(declare-fun T () Int)
(assert (and (<= 1 T) (< T P)))     ; nonzero field element
(assert (forall ((I Int))
   (=> (and (<= 0 I) (< I P))
       (not (= (mod (* I T) P) 1)))))
(check-sat)
