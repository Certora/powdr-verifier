; rule slug: forall-witness-instantiation
; pass: witness  (src/simplify/witness.py :: WitnessSubstituter.walk_forall / simplify_witnesses)
; contract intended by transform: (claimed) equisat replacement of an asserted
;   (forall q0..qk. Body(q0..qk))  by its SINGLE instance  Body(free_var,...,free_var)
;   i.e. every quantified marker qvar is substituted by the SAME concrete term `free_var`
;   taken from a collapsed top-level witness assert, and the whole forall binder is dropped.
;
; WHAT IS CHECKED HERE (equivalence direction / entailment):
;   Does the retained single instance  Body(free_var)  ENTAIL the universal  (forall q. Body(q))?
;   The transform replaces the universal by the instance; for that to preserve the
;   constraint content (equivalence) we would need  instance  <=>  universal.
;   Universal ALWAYS entails instance; the open question is the reverse. We check the reverse:
;     assert  Body(v)            (the kept instance)
;     assert  (not forall q Body(q))
;   Body(q) is the witness atom  cmp == q*(f0+f1)  (mod P), matching _match_expanded_witness
;   where each qvar_i multiplies a factor symbol and cmp is the lone compare symbol.
;
; EXPECTED: sat.
;   sat = counterexample = the instance does NOT entail the universal, so the rewrite is
;         STRICTLY WEAKER as an asserted hypothesis (it silently DROPS the constraints that
;         the universal imposes, e.g. f0+f1==0 and cmp==0). Hence the rewrite is NOT an
;         equivalence and is NOT unconditionally unsat-preserving.
;   A sat model exhibits cmp,f0,f1,v with cmp==v*(f0+f1) yet some q with cmp != q*(f0+f1).
; (unsat would have meant instance<=>universal, i.e. the rewrite is faithful.)

(declare-const cmp Int)
(declare-const f0 Int)
(declare-const f1 Int)
(declare-const v Int)

; field-Int domain: elements in [0,P), P=97
(assert (and (<= 0 cmp) (< cmp 97)
             (<= 0 f0)  (< f0 97)
             (<= 0 f1)  (< f1 97)
             (<= 0 v)   (< v 97)))

; kept instance Body(v):  cmp == v*(f0+f1)  (mod 97)
(assert (= (mod (- cmp (+ (* v f0) (* v f1))) 97) 0))

; negation of the universal the transform discards:  NOT forall q. cmp == q*(f0+f1)
(assert (not (forall ((q Int))
   (=> (and (<= 0 q) (< q 97))
       (= (mod (- cmp (+ (* q f0) (* q f1))) 97) 0)))))

(check-sat)
(get-value (cmp f0 f1 v))
