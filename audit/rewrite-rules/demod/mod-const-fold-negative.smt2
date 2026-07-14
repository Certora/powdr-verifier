; rule slug: mod-const-fold  (latent-bug variant: NEGATIVE modulus)
; source: walk_mod const branch (demod.py:243-245), guard is `mc != 0` (not `> 0`)
; What is checked: for m = -5, c = 3, the folder would emit Int(3 % -5).
;   Python: 3 % -5 == -2 ;  SMT-LIB (mod 3 -5) == 3 (0 <= r < 5).
;   So the folded constant (-2) differs from the true SMT value (3).
; EXPECTED: sat  => demonstrates the fold is WRONG for negative modulus.
;   (Reachable only if a negative literal modulus ever appears; believed unreachable
;   in practice, so this is a latent/defensive-gap finding, not a live unsoundness.)
; A 'sat' model just confirms 3 (SMT) != -2 (Python fold).
(set-logic QF_NIA)
(assert (not (= (mod 3 (- 5)) (- 2))))   ; SMT value is 3, not the folded -2
(check-sat)
