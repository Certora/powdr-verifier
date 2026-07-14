; rule slug: mod-push-ite
; source: walk_mod ite branch (demod.py:246-261)
;   Mod(Ite(cond, t, e), m) --> Ite(cond, Mod(t,m), Mod(e,m))
; contract: equivalence.  Mod distributes over Ite trivially (Ite picks one branch).
; What is checked: for all cond,t,e the two forms are equal (m=97).
; EXPECTED: unsat  => sound.  A 'sat' model would break Ite distributivity (bug).
(set-logic QF_NIA)
(declare-fun cond () Bool)
(declare-fun t () Int)
(declare-fun e () Int)
(assert (not (= (mod (ite cond t e) 97)
                (ite cond (mod t 97) (mod e 97)))))
(check-sat)
