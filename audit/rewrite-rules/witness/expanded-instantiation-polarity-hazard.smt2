; rule slug: expanded-witness-universal-instantiation (POLARITY hazard)
; contract: unsat-preserving (shows the precondition on which soundness rests).
; pass: witness (src/simplify/witness.py, WitnessSubstituter.walk_forall)
;
; WHAT THIS CHECKS: WitnessSubstituter fires on ANY forall node it meets while
;   walking an asserted formula; it does NOT track boolean polarity. Instantiation
;   is a sound weakening ONLY in a POSITIVE (assumption) position. If a matched
;   forall ever sat under a negation -- effectively  Not(forall q. P(q)) = Exists q. Not P(q)
;   -- then replacing it by  Not P(fv)  is a STRENGTHENING and can turn SAT into
;   UNSAT (a false PASS / manufactured proof).
;
;   We exhibit an assignment where the negative-position ORIGINAL is satisfiable
;   (some q makes Not P(q) true) yet the REWRITTEN conjunct Not P(fv) is false
;   (P(fv) holds). Under that assignment original=SAT, rewritten=UNSAT => unsound.
;
; EXPECTED VERDICT: sat  (=> hazard is real for negative positions).
;   NOTE: in the actual pipeline (src/verifier.py:54) the sole forall is the
;   POSITIVE conjunct  And(before, ForAll(q, ...), ...), so this hazard is NOT
;   triggered and the pass is sound as used. A 'sat' here therefore flags a
;   latent requirement ("only instantiate positive foralls"), not a live bug --
;   unless some other pass introduces a forall under a negation before this runs.
;
; Model witness: f0=1 f1=0 cmp=0 fv=0.
(set-logic UFNIA)
(declare-fun f0 () Int)
(declare-fun f1 () Int)
(declare-fun cmp () Int)
(declare-fun fv () Int)
; rewritten negative conjunct requires P(fv) to hold (so Not P(fv) is false):
(assert (= (mod (- (+ (* fv f0) (* fv f1)) cmp) 7) 0))
; original negative conjunct Exists q. Not P(q) is satisfiable:
(assert (exists ((q0 Int) (q1 Int))
          (not (= (mod (- (+ (* q0 f0) (* q1 f1)) cmp) 7) 0))))
(check-sat)
(get-value (f0 f1 cmp fv))
