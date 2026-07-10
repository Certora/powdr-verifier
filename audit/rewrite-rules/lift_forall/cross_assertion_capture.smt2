; rule slug: cross_assertion_capture
; contract: equisat (this validates the FRESHNESS precondition of one_point_lift)
;
; The abstract one-point lift is sound only when the lifted qvar becomes a
; genuinely fresh top-level symbol. The implementation collapses distinct
; quantifiers into ONE shared symbol whenever two forall assertions reuse the
; same bound-variable symbol (same name + type). In pySMT bound variables are
; interned Symbol nodes, so two assertions
;     (assert (forall ((x Int)) (or (not (= x e1)) (P x))))
;     (assert (forall ((x Int)) (or (not (= x e2)) (Q x))))
; share the SAME FNode x. LiftForallWalker.lifted is a dict keyed by that
; symbol, so the second lift OVERWRITES the first: only (= x e2) survives, x is
; declared once, and BOTH surviving bodies P(x), Q(x) now reference that single
; global x. Transformed script is satisfiable iff
;     (exists x. x = e2 /\ P(x) /\ Q(x))  ==  P(e2) /\ Q(e2)
; whereas the correct (fresh-per-quantifier) meaning is
;     P(e1) /\ Q(e2).
; When e1 != e2 and P differs at e1 vs e2 these diverge, and the divergence can
; turn a SAT (counterexample-bearing) assumption set into UNSAT -> false PASS.
;
; CHECK: can the conflated transform (P e2 /\ Q e2) disagree with the intended
; meaning (P e1 /\ Q e2)?  Asserted as their non-equivalence.
; EXPECTED: sat  => the capture is a real unsoundness hazard (a model where the
; two differ; concretely e1 != e2, P true only at e1). This does NOT prove the
; hazard is reached in practice (depends on whether powdr reuses bound-var names
; across assertions) but shows the implementation lacks the freshness guard the
; rule requires. 'unsat' would mean no such divergence exists (it does).
(set-logic UFLIA)
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
; intended (fresh) meaning: each quantifier pins its own copy
(define-fun INTENDED () Bool (and (P e1) (Q e2)))
; implementation with shared symbol x forced to the last pin e2
(define-fun CONFLATED () Bool (and (P e2) (Q e2)))
(assert (not (= INTENDED CONFLATED)))
(check-sat)
(get-value (e1 e2))
