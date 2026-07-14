; rule slug: top-eq-elim
; pass: solve_eqs  (src/simplify/solve_eqs.py, simplify_solve_eqs / _pick_elim_target)
; contract: EQUISAT (top-level free-variable elimination = one-point rule)
;
; RULE: given a top-level conjunctive equality (= x e) where x is a declared
;   (existentially quantified) symbol, x does not occur in e (acyclic), and e
;   contains no array-store, substitute x := e everywhere, drop the equality,
;   and drop x's declaration.
;
; Direction that matters for the verifier: the transform must not turn a SAT
;   (counterexample-bearing) script into an UNSAT one (that would manufacture a
;   false PASS). Equisat covers both directions. Here we check the exact
;   one-point equivalence that the whole pass reduces to:
;       (exists x. (x=e /\ Q(x) /\ D(x)))  <=>  (Q(e) /\ D(e))
;   where Q,D are arbitrary contexts / domain constraints mentioning x, and e is
;   x-free. Substitution correctly carries domain constraints D(x) onto e.
;
; EXPECTED: unsat  => the two sides are logically equal for all a,b => rule SOUND.
;   A 'sat' model would exhibit a,b for which eliminating x changes satisfiability
;   of the script (a false PASS / false FAIL) => UNSOUND.
;
; P = 97 (small field stand-in). Soundness is pure logic and does NOT depend on P
;   being BabyBear, so no babybear variant is needed.
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(define-fun P () Int 97)
; e is x-free (the acyclicity guard). Uses field mod to mimic real value exprs.
(define-fun e () Int (mod (* a b) P))
; Q(x): an arbitrary field-equality context mentioning x.
(define-fun Q ((v Int)) Bool (= (mod (+ v a) P) 0))
; D(x): domain constraint on x (0 <= x < P), also gets the substitution.
(define-fun D ((v Int)) Bool (and (<= 0 v) (< v P)))
; a,b constrained to the field domain (harmless; keeps things concrete).
(assert (and (<= 0 a) (< a P) (<= 0 b) (< b P)))
; transformed script (x eliminated, equality dropped, D carried onto e):
(define-fun Ftrans () Bool (and (Q e) (D e)))
; original script existentially closed over x:
(assert (not (= (exists ((x Int)) (and (= x e) (Q x) (D x))) Ftrans)))
(check-sat)
