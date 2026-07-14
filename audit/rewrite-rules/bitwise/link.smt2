; rule: link  (_ground_linking_lemmas: added AXIOMS tying xor/and/or)
; contract: unsat-preserving  (axiom must hold in every intended (byte) model,
;           else a real SAT counterexample can be pruned -> spurious PASS)
; guard in code: 0<=x<=255 and 0<=y<=255. Modeled with 8-bit BV = exactly the
; byte domain, so the guard is intrinsic and the check is decidable.
; lemmas: (1) x+y = (x^y) + 2*(x&y)
;         (2) 0 <= x&y <= x  and  x&y <= y
;         (3) x|y = x+y-(x&y),  0 <= x|y <= 255
; EXPECTED: unsat = sound. sat = a byte pair where an axiom is FALSE.
(set-logic ALL)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(define-fun X   () Int (bv2nat x))
(define-fun Y   () Int (bv2nat y))
(define-fun XOR () Int (bv2nat (bvxor x y)))
(define-fun AND () Int (bv2nat (bvand x y)))
(define-fun OR  () Int (bv2nat (bvor  x y)))
(assert (or
  (not (= (+ X Y) (+ XOR (* 2 AND))))
  (not (and (<= 0 AND) (<= AND X) (<= AND Y)))
  (not (and (= OR (- (+ X Y) AND)) (<= 0 OR) (<= OR 255)))))
(check-sat)
