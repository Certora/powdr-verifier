; rule slug: self-mod-witness
; source: _self_mod_symbol + extract_symbol_ranges (demod.py:28-42, 134-139)
;   A top-level assertion  x = mod(x, m)  (or mod(x,m) = x) is taken as a witness
;   for the range 0 <= x <= m-1, and the assertion is added to `protected`.
; contract: the derived range must be entailed by the witness (soundness of the
;   learned fact).  Since the fact feeds mod-elim, we need: (x = mod(x,m)) => 0<=x<m.
; What is checked: (x = mod(x,m))  <=>  (0 <= x < m)  for m=97 (>0).
;   Euclidean mod gives mod(x,m) in [0,m); equality with x holds iff x already in [0,m).
; EXPECTED: unsat  => the witness exactly characterizes the range; sound.
;   A 'sat' model would be an x where the equality holds but x is outside [0,m)
;   (or vice versa) -- i.e. the learned range is unjustified (bug).
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (not (= (= x (mod x 97))
                (and (<= 0 x) (< x 97)))))
(check-sat)
