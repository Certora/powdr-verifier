; rule slug: eqmod-zero-solve
; source: _demod_rewrite_eqmod_zero_equals / _EqModZeroWalker (demod.py:92-122)
; contract intended by author: equivalence (over field elements)
; ACTUAL rewrite:  Mod(a*x + b, p) = 0   -->   x = ((-b) * a^{-1} mod p)
;   applied UNCONDITIONALLY at every Equals node, with NO range guard on x.
; What is checked: is the rewrite an equivalence for an integer-typed x that is
;   NOT known to lie in [0,p)?  (The sibling DeModSubstituter path checks a range
;   before dropping mod; this path does not.)
; Encoding: small prime p=97, a=1, b=3  =>  val = (-3) mod 97 = 94.
;   A (original) :  (= (mod (+ x 3) 97) 0)
;   B (rewritten):  (= x 94)
; We look for a model of A that is NOT a model of B (x = -3 works: mod(0,97)=0).
; EXPECTED: sat  => the rewrite STRENGTHENS the assertion (drops integer models
;   x = val + k*p), so a SAT VC (real counterexample using x=-3) becomes UNSAT.
;   This is the false-PASS / unsound direction.  A 'sat' model is such a witness.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (= (mod (+ x 3) 97) 0))   ; A holds
(assert (not (= x 94)))           ; B fails
(check-sat)
(get-value (x))
