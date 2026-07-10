; rule slug: pin-eq-lift-single
; pass: lift_forall
; contract: equivalence (equisat is the operative direction for the VC)
;
; WHAT THE PASS DOES (core rewrite):
;   A disjunct (not (= q expr)) inside a  (forall (q ...) (or ... ))
;   body, where q is a quantified variable and expr has NO free occurrence
;   of any quantified variable, is peeled off:
;     forall q. ( (q != expr) | rest(q) )
;   becomes: a fresh top-level constant q with top-level  (= q expr),
;   and the quantifier over q is dropped (rest(q) keeps q, now free).
;
; This validator checks the algebraic identity underlying the peel in
; ISOLATION (unique variable name, closed expr, no top-level collision):
;     forall q. (q != e | P(q))   ===   ( exists q. q = e & P(q) )   ===  P(e)
;
; CHECK: assert the source form and the substituted form differ -> expect UNSAT.
; EXPECTED VERDICT: unsat  => sound (the peel is a logical equivalence here).
;   A 'sat' model would exhibit an interpretation where the quantified
;   disjunction and the pinned/substituted form disagree = unsound.

(set-logic UFLIA)
(declare-fun e () Int)          ; the closed pin expression
(declare-fun P (Int) Bool)      ; the remaining body 'rest', depends on q

; source: forall q. ( (q != e) | P(q) )
(define-fun SRC () Bool
  (forall ((q Int)) (or (not (= q e)) (P q))))

; result of the peel: pin q=e (fresh const) and keep P(q). Equivalent to P(e).
(define-fun DST () Bool (P e))

(assert (not (= SRC DST)))
(check-sat)
