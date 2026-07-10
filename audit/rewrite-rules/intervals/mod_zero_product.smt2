; rule slug: mod_zero_product
; pass: intervals   file: src/simplify/intervals/reasoner.py  _refine_from_mod_zero (lines 519-549)
; contract: unsat-preserving NARROWING for  (= (mod (* u1 ... uk) P) 0).
;   Prime-field fact: product == 0 (mod P) => SOME factor == 0 (mod P).
;   The code, for every unit-coefficient single-symbol factor sym+c0 whose domain
;   is canonical [0,P), computes the residue that zeroes THAT factor and INTERSECTS
;   sym's domain with {that residue}. When >=2 DISTINCT symbols occur across factors
;   it forces EVERY symbol to its zero-residue simultaneously (x==0 AND y==0),
;   i.e. it treats an OR as an AND.
;
; Concrete instance (P=7): atom  (= (mod (* x y) 7) 0), with 0<=x<7, 0<=y<7.
;   The rule derives  x==0  AND  y==0.
;
; CHECK: is (x==0 AND y==0) IMPLIED by (0<=x<7 AND 0<=y<7 AND (mod (x*y) 7)=0)?
;   Assert the hypotheses AND the negation  NOT(x=0 AND y=0).
; EXPECTED: sat  => the conjunction x=0 AND y=0 is NOT implied => UNSOUND narrowing.
;   A 'sat' model (e.g. x=0,y=3 or x=3,y=0) satisfies the atom but is wrongly
;   removed by forcing the other variable to 0.  (Bug is P-independent; small P used.)
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 0 x)) (assert (< x 7))
(assert (<= 0 y)) (assert (< y 7))
(assert (= (mod (* x y) 7) 0))
; negation of the reasoner's derived conjunction (x=0 AND y=0)
(assert (not (and (= x 0) (= y 0))))
(check-sat)
(get-model)
