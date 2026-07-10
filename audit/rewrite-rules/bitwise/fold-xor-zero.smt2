; rule slug: fold-xor-zero
; pass: bitwise  (walk_function constant-fold for UF_XOR)
; contract: equivalence (term rewrite UF_XOR(x,y) -> simpler term)
; rewrite: UF_XOR(x,0)->x ; UF_XOR(0,y)->y ; UF_XOR(x,x)->0
; WHAT IS CHECKED: that the byte-wise XOR (ground truth = bvxor) satisfies
;   x^0=x, 0^y=y, x^x=0.  If it does, the fold cannot kill a genuine
;   counterexample (the real model still satisfies the substituted equality),
;   so the rewrite is sound.
; DOMAIN: bytes (8-bit). Identities are width-independent, so bytes suffice;
;   the rule itself is emitted unguarded but these hold for all nonneg ints.
; EXPECTED: unsat  (unsat = no violation = SOUND).
;   A sat model would be a byte where real XOR disagrees with the fold => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(assert (or
  (not (= (bvxor X #x0000) X))
  (not (= (bvxor #x0000 Y) Y))
  (not (= (bvxor X X) #x0000))))
(check-sat)
