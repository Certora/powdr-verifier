; rule slug: store-def-elim (OR-context substitution + refl fold), the motivating case
; pass: solve_store_eqs
; contract: equivalence (substitution under a top-level equality inside a disjunction)
;   Motivating shape from the docstring: a top-level (= arr S) plus a negated form
;   (not (= arr S2)) sitting inside an (or ...). After arr:=S substitution the negated
;   form becomes (not (= S S2)); when S2 is the SAME store expression as S the _FoldRefl
;   walker collapses (= S S) -> True, (not True) -> False, and the disjunct drops.
;
; WHAT IS CHECKED: under (= arr S), the OR body before substitution
;     (or D (not (= arr S2)))
;   is equivalent to the OR body after substitution
;     (or D (not (= S  S2))).
;   Assert (= arr S) and (not (<=> before after)); expect UNSAT.
;   Holds for ANY S2 (whether or not S2 is syntactically S); the syntactic-refl fold is a
;   special case that the equivalence subsumes.
;
; EXPECTED: unsat => sound. A sat model would mean substituting arr:=S inside the OR
;   changed the meaning of the disjunction while (= arr S) held -- unsound.
(set-logic ALL)

(declare-fun arr  () (Array Int (Array Int Int)))
(declare-fun base () (Array Int (Array Int Int)))
(declare-fun base2 () (Array Int (Array Int Int)))
(declare-fun inner () (Array Int Int))
(declare-fun inner2 () (Array Int Int))
(declare-fun k () Int)
(declare-fun k2 () Int)
(declare-fun D () Bool)

(define-fun S  () (Array Int (Array Int Int)) (store base  k  inner))
(define-fun S2 () (Array Int (Array Int Int)) (store base2 k2 inner2))

(assert (= arr S))

(define-fun before () Bool (or D (not (= arr S2))))
(define-fun after  () Bool (or D (not (= S   S2))))

(assert (not (= before after)))
(check-sat)
