; rule: choice-disjunction (bounded decidable variant of choice-disjunction.smt2)
; Both sides depend only on residues mod 7, so ranging each var over [0,7) covers all
; residue classes and soundly decides the equivalence. EXPECTED: unsat (sound).
(set-logic QF_NIA)
(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)(declare-fun x () Int)
(assert (and (<= 0 a)(< a 7)(<= 0 b)(< b 7)(<= 0 c)(< c 7)(<= 0 x)(< x 7)))
(define-fun A () Bool (= (mod (* a (* b c)) 7) 0))
(define-fun B () Bool (or (= (mod a 7) 0) (= (mod b 7) 0) (= (mod c 7) 0)))
(define-fun Ap () Bool (= (mod (* x (* (- x 1) (- x 2))) 7) 0))
(define-fun Bp () Bool (or (= (mod x 7) 0) (= (mod (- x 1) 7) 0) (= (mod (- x 2) 7) 0)))
(assert (or (not (= A B)) (not (= Ap Bp))))
(check-sat)
