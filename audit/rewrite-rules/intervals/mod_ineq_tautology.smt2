; rule slug: mod_ineq_tautology
; pass: intervals   file: src/simplify/intervals/reasoner.py  _mod_ineq_is_tautology (lines 351-371)
; contract: 'other' -- these are recognized tautologies about (mod E P) in [0,P-1];
;   used only to SKIP refinement, so at worst a false positive loses precision. Still,
;   we verify each recognized pattern is genuinely valid over Euclidean mod.
;
; Patterns (P=7):
;   0 <= (mod E 7)            [a==0, le, bm branch]
;   -1 < (mod E 7)            [a<0 const, strict, bm branch]     (a = -1)
;   (mod E 7) <= 6            [b==P-1, le, am branch]
;   (mod E 7) < 7             [b==P,   strict, am branch]
;
; CHECK: assert the negation of the conjunction of all four over arbitrary E.
; EXPECTED: unsat  => all four are tautologies => SOUND recognition.
(set-logic QF_NIA)
(declare-fun E () Int)
(assert (not (and
  (<= 0 (mod E 7))
  (< (- 1) (mod E 7))
  (<= (mod E 7) 6)
  (< (mod E 7) 7))))
(check-sat)
