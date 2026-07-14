; rule slug:   skolem-instantiate-forall
; contract:    unsat-preserving (this is the CORE skolem mechanism)
; pass:        skolem-core (src/simplify/skolem.py walk_forall + emit_disjuncts,
;              then src/simplify/lift_forall.py hoists the pin)
;
; WHAT THE PASS DOES (net effect):
;   A forall in NNF (positive/monotone position; guaranteed by the
;   nnf:skolem:lift pipeline order) has body Or(D...). The pass appends a
;   disjunct  Not(q = w)  for a chosen witness w, giving
;       forall q. ( D(q) \/ q != w ).
;   lift_forall then removes q from the prefix, declares q as a fresh free
;   symbol, and asserts (q = w) at top level. Net:  D(q) /\ q = w  == D(w).
;   i.e. the universal is INSTANTIATED at the witness point w.
;
; WHY IT SHOULD BE SOUND (no false PASS):
;   A false PASS = turning a SAT (counterexample-bearing) VC into UNSAT.
;   Instantiation only WEAKENS a positively-occurring universal:
;       (forall q. D(q))  implies  D(w)   for ANY w.
;   So models(original) subset of models(transformed); a SAT VC stays SAT.
;   Soundness therefore does NOT depend on w being a "correct" witness --
;   witness quality only affects completeness (whether an UNSAT stays UNSAT).
;
; WHAT IS CHECKED HERE:
;   Universal instantiation is valid for an arbitrary predicate D and an
;   arbitrary witness w:  assert (forall q. D q) and (not (D w)); if this is
;   UNSAT for uninterpreted D and arbitrary w, instantiation is sound.
;
; EXPECTED: unsat  (sound).  A 'sat' model would be a predicate/witness where
;   the universal holds but its instance fails -- impossible in FOL; a sat here
;   would mean the mechanism is NOT plain instantiation (i.e. a real bug).

(set-logic UFLIA)
(declare-fun D (Int) Bool)
(declare-fun w () Int)

(assert (forall ((q Int)) (D q)))
(assert (not (D w)))

(check-sat)
