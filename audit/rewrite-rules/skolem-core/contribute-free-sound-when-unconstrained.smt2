; rule slug: skolem-rules-contribute_free  (soundness UNDER the precondition)
; contract: unsat-preserving / equisat
; pass: skolem-core (src/simplify/skolem_rules.py:contribute_free)
;
; WHAT IS CHECKED:
;   The precondition that makes contribute_free sound: the free var v is genuinely
;   UNCONSTRAINED by the remaining assumptions Phi (Phi does not mention v). Then
;   Phi(v) is independent of v, so
;       (exists v. Phi(v))  ==  Phi   ==  Phi(e)
;   and adding (v = e) is equisat (removes no model). We model Phi by a boolean B
;   that does not mention v, and check the negated soundness lemma
;       (exists v. Phi) /\ not Phi(e)  ==  B /\ not B.
; EXPECTED: unsat (sound).  Confirms that WHEN the code's stated invariant holds
;   (v unconstrained), the top-level pin is sound. A 'sat' would contradict that.
;
; NOTE: this file establishes only the CONDITIONAL soundness. Whether the
;   invariant actually holds for after-diff_val -- i.e. no residual bus consumer
;   or output constraint forces a value != e -- is a property of the VC generator
;   and the powdr optimizer's equivalence proof, NOT checkable from these files.
;   Verdict for the rule is therefore 'uncertain' (leans sound in practice given
;   memory: bus matching is by timestamp, not data, so diff_val's data is not
;   force-matched across circuits).
(set-logic UFLIA)
(declare-fun B () Bool)
; (exists v. B)  and  not B(e)   -- v does not occur in B, so this is B /\ ~B
(assert (and B (not B)))
(check-sat)
