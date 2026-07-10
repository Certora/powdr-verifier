; rule: choice-disjunction
; source: rewrites.py rewrite_choice_simple (Or branch) / rewrites_sympy.py rewrite_choice (Or branch)
; transform: Mod(f1*f2*...*fn, p) == 0   -->   Or_i (Mod(fi, p) == 0)
; contract: EQUIVALENCE (atom replaced in arbitrary polarity in the VC)
; what is checked: over a PRIME field the product is 0 mod p iff some factor is 0 mod p
;   (integral-domain zero-product property). Uses P = 7 (prime). No range constraint on
;   the variables is needed: the identity holds for ALL integers.
; EXPECTED: unsat  (sound). A 'sat' model would be integers where the product is 0 mod p
;   but no factor is (would refute the integral-domain property / factorization).
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun x () Int)
; generic 3-factor zero-product over Z/7Z
(define-fun A () Bool (= (mod (* a (* b c)) 7) 0))
(define-fun B () Bool (or (= (mod a 7) 0) (= (mod b 7) 0) (= (mod c 7) 0)))
; polynomial instance: e = x*(x-1)*(x-2), factored form is what the rule emits
(define-fun Ap () Bool (= (mod (* x (* (- x 1) (- x 2))) 7) 0))
(define-fun Bp () Bool (or (= (mod x 7) 0) (= (mod (- x 1) 7) 0) (= (mod (- x 2) 7) 0)))
(assert (or (not (= A B)) (not (= Ap Bp))))
(check-sat)
