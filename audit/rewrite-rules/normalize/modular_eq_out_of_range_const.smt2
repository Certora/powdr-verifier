; rule: modular_eq_out_of_range_const  (LATENT gap in the modular-equality path)
;   normalize.walk_equals (modular) via relation_poly_diff / _relation_modular.
; contract: equivalence  (A <=> B)  -- required, because _NormalizeWalker is a DAG
;   walker over the FULL boolean structure, so a rewritten relation can sit under
;   an arbitrary number of negations; only true equivalence is polarity-safe.
;
; What triggers it: _relation_modular returns True for (= (mod a P) C) whenever C
;   is ANY Int constant (guard: `lhs_m and _as_int_const(rhs) is not None`), with
;   NO check that 0 <= C < P.  _expr_to_poly then reduces C mod P, so the rewrite
;   becomes  (= (mod (a - C) P) 0)  ==  (a == C (mod P)).
;
;   For C in [0,P) this is exactly equivalent to the original.
;   For C OUTSIDE [0,P) it is NOT: Euclidean (mod a P) lies in [0,P), so the
;   ORIGINAL (= (mod a P) C) is UNSATISFIABLE, while the rewrite (a == C mod P)
;   is satisfiable. A model of the rewrite need not model the original -> under a
;   negation this REMOVES models -> can manufacture UNSAT -> false PASS = UNSOUND.
;
; Concrete instance: C = 100, P = 97  (100 mod 97 = 3).
;   A = (= (mod a 97) 100)  -- always false.
;   B = (= (mod (- a 100) 97) 0) == (a == 3 mod 97).
; EXPECTED: sat  (=> the two are NOT equivalent; the rewrite is unsound *iff this
;   input shape is reachable*). Model: a=3 makes B true, A false.
;
; REACHABILITY: the current encoder only emits modular equalities with RHS 0
;   (wrap_mod(...) == Int(0)) or declines on symbol/mod-wrapped RHS, so C is
;   always 0 (in range) in practice -> field_eq_monic is SOUND as used today.
;   This file documents a latent robustness gap: a missing 0<=C<P guard.
(set-logic QF_NIA)
(declare-const a Int)
(define-fun P () Int 97)
(assert (not (= (= (mod a P) 100)
                (= (mod (- a 100) P) 0))))
(check-sat)
