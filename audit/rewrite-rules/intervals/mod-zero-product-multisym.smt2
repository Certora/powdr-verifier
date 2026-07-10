; rule: mod_zero_product  (_refine_from_mod_zero, is_times branch, reasoner.py:519-549)
; contract: sound narrowing.  (u1*...*uk) == 0 (mod p), p prime, over factors that are
;   affine unit-coefficient in canonical [0,p) symbols.  Correct fact: SOME factor == 0
;   (mod p)  (a DISJUNCTION).  The code instead narrows EACH symbol independently to its
;   own root residue set, i.e. it asserts the CONJUNCTION "x is a root AND y is a root".
; INSTANCE: p=7, factors x and y, both in [0,6].  Product (x*y) mod 7 = 0.
;   Code sets candidates[x]={0}, candidates[y]={0} and narrows x->{0} AND y->{0}.
;   (Verified empirically: adding x=3 makes the env bottom => whole script -> false => UNSAT.)
; CHECK: is the derived conjunction (x=0 AND y=0) implied by (ranges and (x*y) mod 7 = 0)?
; EXPECTED: sat => UNSOUND. A sat model (e.g. x=0,y=3) satisfies product==0 but not
;   (x=0 and y=0): the product rule's per-symbol narrowing is not implied by the disjunction.
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= 0 x) (<= x 6)))
(assert (and (<= 0 y) (<= y 6)))
(assert (= (mod (* x y) 7) 0))
(assert (not (and (= x 0) (= y 0))))   ; negation of the rule's per-symbol narrowing
(check-sat)
(get-value (x y))
