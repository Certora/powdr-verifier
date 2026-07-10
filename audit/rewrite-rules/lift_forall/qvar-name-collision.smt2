; rule slug: qvar-name-collision
; pass: lift_forall
; contract: equisat / unsat-preserving  (VC must stay SAT if original is SAT)
;
; WHAT / WHY THIS IS THE SOUNDNESS HOLE:
;   LiftForallWalker.lifted is a dict keyed by the QUANTIFIED SYMBOL node.
;   In pysmt a Symbol is interned by (name,type): two independent
;   quantifiers  (forall ((q Int)) ...)  and  (forall ((q Int)) ...)  in the
;   script bind the SAME FNode q. If both peel a pin for q with DIFFERENT
;   exprs, self.lifted[q] is OVERWRITTEN (last write wins) and only ONE
;   top-level (= q expr) is emitted, while BOTH forall bodies are rewritten
;   to reference the single free top-level q. Result: one forall's body is
;   substituted with the OTHER forall's pin value -> wrong substitution ->
;   can turn a SAT (counterexample-bearing) assumption set into UNSAT
;   = a manufactured false PASS.
;
; Concrete model of the two asserts:
;   ORIG  =  (forall q. q!=a | S(q)) & (forall q. q!=b | T(q))   ==  S(a) & T(b)
;   TRANS =  exists q. (q=b) & S(q) & T(q)                        ==  S(b) & T(b)
;            (q=b is the surviving pin; both bodies now read the shared q)
;
; CHECK: is there an interpretation where ORIG holds (original assumptions
;   consistent = verifier should find a counterexample, NOT prove) yet TRANS
;   fails (transformed set refuted = falsely "proven")?
;     assert  a != b, ORIG, (not TRANS)   -> expect SAT.
; EXPECTED VERDICT: sat => UNSOUND when the collision is reachable
;   (two same-named same-typed bound vars pinned to different exprs).
;   A sat model IS the manufactured-false-PASS witness.

(set-logic UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun S (Int) Bool)
(declare-fun T (Int) Bool)

(define-fun ORIG () Bool
  (and (forall ((q Int)) (or (not (= q a)) (S q)))
       (forall ((q Int)) (or (not (= q b)) (T q)))))

(define-fun TRANS () Bool
  (exists ((q Int)) (and (= q b) (S q) (T q))))

(assert (not (= a b)))
(assert ORIG)
(assert (not TRANS))
(check-sat)
