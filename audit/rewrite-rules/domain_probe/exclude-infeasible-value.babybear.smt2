; rule slug:   exclude-infeasible-value  (BabyBear P variant)
; pass:        domain_probe
; contract:    unsat-preserving / equisat (learn an implied unit fact)
;
; Same check as exclude-infeasible-value.smt2 but with the real BabyBear prime.
; The subset rel pins x == 10 (mod P); we then ask if the full set F admits
; x = 5. Injected fact (x != 5) must be entailed by F.
;
; EXPECTED: unsat (= sound). A 'sat' model would exhibit F allowing an
;   excluded value == UNSOUND. May be slower than the P=97 variant.

(set-logic QF_NIA)
(define-fun P () Int 2013265921)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (or (= x 5) (= x 10) (= x 20)))
(assert (= (mod (- x 10) P) 0))
(assert (= (mod (- y 3) P) 0))
(assert (= x 5))

(check-sat)
