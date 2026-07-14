; rule slug: one-point-elim
; pass: solve_eqs
; contract: equisat (variable elimination / one-point rule for a free/top-level
;   existentially-quantified symbol x). Direction that matters for the verifier:
;   both -- the transform must preserve satisfiability exactly (original UNSAT
;   <=> rewritten UNSAT), because the VC is checked for UNSAT.
;
; WHAT THE RULE DOES:
;   Given the whole assertion set (a top-level conjunction) that contains, in a
;   purely conjunctive context, an equality (= x e) where
;     (1) x is a declared (free, top-level existential) symbol,
;     (2) e does not mention x (acyclic),
;     (3) [engineering guard, not soundness] e has no array store,
;   it substitutes x := e everywhere, drops the equality (folds to True), and
;   drops x's declaration.
;
; NOTE ON SEMANTICS: the eliminated equality is STRUCTURAL SMT (= a b), NOT the
;   modular field equality (= (mod (- a b) P) 0). So the mod/order/sign hazards
;   do NOT apply to this pass -- the one-point rule for plain = is field-agnostic.
;
; WHAT IS CHECKED HERE: the one-point rule SCHEMA, in full generality.
;   P (Int Int) Bool  models an arbitrary body Phi(x, y).
;   e (Int) Int       models the witness expression; it depends only on y, which
;                     ENCODES guard (2) "e does not mention x".
;   Claim:  ( exists x. (x = e(y)) /\ Phi(x,y) )  <=>  Phi(e(y), y)   for all y.
;
; EXPECTED VERDICT: unsat  = the negation is unsatisfiable = rule is SOUND.
;   A 'sat' model would be a y (and interpretations of P,e) where the eliminated
;   formula and the substituted formula disagree = the substitution is unsound.

(set-logic UFLIA)
(declare-fun P (Int Int) Bool)
(declare-fun e (Int) Int)

(assert (not
  (forall ((y Int))
    (= (exists ((x Int)) (and (= x (e y)) (P x y)))
       (P (e y) y)))))

(check-sat)
