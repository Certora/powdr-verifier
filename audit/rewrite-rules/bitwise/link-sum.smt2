; rule slug: link-sum
; pass: bitwise  (_ground_linking_lemmas conjunct 1)
; contract: unsat-preserving (adds an axiom to the UNSAT-checked VC).
;   Sound iff the axiom is TRUE for the real byte-wise ops: then genuine
;   counterexamples survive and no false PASS can be manufactured.
; axiom (byte-guarded): x + y = uf_xor(x,y) + 2*uf_and(x,y)
; WHAT IS CHECKED: does the identity hold for real bytes with real xor/and?
;   Integer arithmetic (no mod): x+y <= 510 < P, so plain Int Plus is exact.
; EXPECTED: unsat  (unsat = SOUND). sat = a byte pair violating the carry
;   identity => the axiom is false => it could kill a real counterexample => unsound.
(set-logic QF_BV)
(declare-fun bx () (_ BitVec 8))
(declare-fun by () (_ BitVec 8))
(define-fun X () (_ BitVec 16) ((_ zero_extend 8) bx))
(define-fun Y () (_ BitVec 16) ((_ zero_extend 8) by))
(define-fun XOR () (_ BitVec 16) (bvxor X Y))
(define-fun AND () (_ BitVec 16) (bvand X Y))
(assert (not (= (bvadd X Y) (bvadd XOR (bvmul #x0002 AND)))))
(check-sat)
