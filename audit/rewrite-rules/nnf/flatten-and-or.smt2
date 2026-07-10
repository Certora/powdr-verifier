; rule slug: flatten-and-or
; pass: nnf  (_flatten_and / _flatten_or: hoist nested same-op args; []->TRUE/FALSE; [a]->a)
; contract: equivalence (boolean) -- associativity/flattening of And/Or.
; transform: And(a, And(b,c), d) -> And(a,b,c,d) ;  Or(a, Or(b,c)) -> Or(a,b,c)
;   plus the identity elements: empty And -> true, empty Or -> false, singleton -> itself.
; check: nested-vs-flat equivalence for both And and Or in one conjunction of checks.
; EXPECTED: unsat => sound.
;   A 'sat' model would mean flattening changed the boolean function.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or
  (not (= (and a (and b c) d) (and a b c d)))
  (not (= (or  a (or  b c) d) (or  a b c d)))
  (not (= (and true a) a))      ; empty-And identity element is true
  (not (= (or  false a) a))))   ; empty-Or identity element is false
(check-sat)
