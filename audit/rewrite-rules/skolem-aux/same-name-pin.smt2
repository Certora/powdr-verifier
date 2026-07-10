; rule slug: same-name-pin  (skolem_names.py::contribute)
; pass: skolem-aux
; contract: unsat-preserving (Skolem-witness selection)
;
; RULE
; ----
; For an unpinned, program-style qvar q (contains '@' after stripping
; before-/after-) of a forall, if a script-declared symbol q' with the same
; stripped name exists (q'!=q, q' not a qvar, matching type), pin q := q'.
; Materialized as the appended disjunct  q != q'  in the forall body.
;
; WHAT IS BEING CHECKED
; ---------------------
; The witness q' is a HEURISTIC (same-name across before-/after-); it may be the
; wrong value for a given assignment of the free variables. We model q' as an
; arbitrary free Int 'other'. Soundness requires only that adding the disjunct
; weakens:  (forall q. body q) => (forall q. body q or q != other).
; Here body is an actual field predicate over BabyBear-shaped mod arithmetic
; (P=7) so the check also exercises the Int/mod domain, not just booleans.
;
; EXPECTED: unsat (implication valid => sound; wrong same-name witness only
; costs completeness, i.e. a spurious sat, never a false PASS).

(set-logic UFLIA)
(define-fun P () Int 7)
(declare-fun other () Int)
(declare-fun k () Int)       ; a free field element the body depends on
(define-fun body ((q Int)) Bool (= (mod (+ (* 3 q) k) P) 0))

(assert (forall ((q Int)) (body q)))
(assert (not (forall ((q Int)) (or (body q) (not (= q other))))))
(check-sat)
