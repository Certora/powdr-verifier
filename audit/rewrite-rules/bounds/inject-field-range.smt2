; rule slug: inject-field-range
; pass: bounds  (src/simplify/bounds.py, field_symbol in src/smt/utils.py:262)
; CONTRACT: unsat-preserving (sound AXIOM INJECTION).
;   The pass ADDS a top-level assertion  0 <= x < P  for every FREE Int symbol
;   whose name ends in @<digits> (a "bounded APC column"). Nothing is removed.
;   Adding an assertion only removes models. Verifier proves equivalence by UNSAT.
;   Soundness therefore reduces to: is the injected axiom a GENUINE invariant of
;   the intended semantics for such a column? If yes, no legitimate distinguishing
;   model is discarded, so UNSAT is preserved and no false PASS is manufactured.
;
; WHAT THIS FILE CHECKS: the positive/soundness case. A true field column is a
;   CANONICAL field element, i.e. x = (mod y P) for some integer y. We check that
;   the injected axiom 0 <= x < P is ENTAILED for any such x -- i.e. the axiom can
;   never be false for a genuine field element, hence its injection removes no real
;   model.  Uses small prime P = 97 (Euclidean mod, matching SMT-LIB semantics).
;
; EXPECTED: unsat  (= axiom is a valid invariant of canonical field elements => the
;   injection is sound for genuine field columns).
;   A 'sat' model would exhibit a canonical field element x=(mod y 97) that violates
;   0<=x<97 -- impossible, so sat would mean the axiom is NOT an invariant (unsound).
(set-logic QF_NIA)
(declare-fun y () Int)
(define-fun P () Int 97)
(define-fun x () Int (mod y P))
; negate the injected axiom for a canonical field element
(assert (not (and (<= 0 x) (< x P))))
(check-sat)
