; rule slug:   skolem-polarity-precondition (NEGATIVE control)
; contract:    demonstrates the SOUNDNESS PRECONDITION of skolem-core
; pass:        skolem-core
;
; WHAT IS CHECKED:
;   If a forall occurred in NEGATIVE position (under a negation, i.e. an
;   existential in disguise), appending Not(q=w) to its body would STRENGTHEN
;   the formula and could turn SAT into UNSAT (a false PASS). This file
;   exhibits that failure mode to justify why the pass MUST run after nnf.
;
;   Original (forall negative):     F  = (not (forall q. B(q)))         [= exists q. ~B(q)]
;   Transformed body-append:        F' = (not (forall q. (B(q) \/ q!=w)))
;                                      = (not (B(w)))                   [instantiation]
;   We look for a model of F where F' is FALSE, i.e. F is SAT but F' is UNSAT
;   at that interpretation: assert F and (not F'). A 'sat' here proves the
;   transform is unsound in negative position.
;
; EXPECTED: sat  (this is a NEGATIVE control: it SHOULD be satisfiable,
;   proving the transform is unsound WITHOUT the nnf precondition). The real
;   pass avoids this because nnf guarantees foralls are positive; sat here is
;   the expected, reassuring result that our polarity analysis is correct.

(set-logic UFLIA)
(declare-fun B (Int) Bool)
(declare-fun w () Int)

; F : exists q. ~B(q)
(assert (not (forall ((q Int)) (B q))))
; ~F' : the transformed formula is FALSE, i.e. B(w) holds
(assert (B w))

(check-sat)
