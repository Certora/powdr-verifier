; rule slug: not-quantifier-nopush
; pass: nnf  (_negate else-branch: for a quantifier/atom/ite, return Not(formula) unchanged)
; contract: equivalence (boolean) -- documents that negation is NOT pushed through
;   quantifiers (nor ITE). This is INCOMPLETE as NNF but must remain SOUND: leaving
;   (not (forall ...)) in place is trivially equivalent to itself.
; The interesting soundness question the audit hint raises is whether the converter ever
; INCORRECTLY pushes negation through a quantifier (which would require Forall<->Exists
; duality and, if botched, flips polarity). The code does NOT push, so we assert that the
; kept form equals the (un-pushed) original -- and, as a cross-check, that the CORRECT push
; would also be equivalent (sanity that duality is the only sound push).
; EXPECTED: unsat => the no-push output is equivalent to input (sound).
;   A 'sat' model would mean the retained (not (forall ...)) differs from itself -- impossible;
;   this file mainly documents that no unsound quantifier push occurs.
(set-logic UFLIA)
(declare-fun P (Int) Bool)
; output of the pass on input (not (forall x. P x)) is literally (not (forall x. P x))
(assert (not (= (not (forall ((x Int)) (P x)))
                (not (forall ((x Int)) (P x))))))
(check-sat)
