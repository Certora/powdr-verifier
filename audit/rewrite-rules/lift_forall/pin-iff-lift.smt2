; rule slug: pin-iff-lift
; pass: lift_forall
; contract: equivalence (boolean variant)
;
; WHAT: same peel but the equality is an Iff over Bool-typed quantified
;   variable (_is_potential_lift_pair accepts (not (iff ...)), and
;   _match_hoistable_eq handles is_iff()). expr is a closed Bool.
;     forall b. ( (b <!=> e) | P(b) )   ->   pin b=e ; P(b)  ==  P(e)
;   (b a Bool qvar; <!=> is negated iff, i.e. the (not (iff b e)) disjunct)
;
; CHECK: assert SRC differs from P(e) -> expect UNSAT.
; EXPECTED VERDICT: unsat => sound.

(set-logic UFLIA)
(declare-fun e () Bool)
(declare-fun P (Bool) Bool)

(define-fun SRC () Bool
  (forall ((b Bool)) (or (not (= b e)) (P b))))

(define-fun DST () Bool (P e))

(assert (not (= SRC DST)))
(check-sat)
