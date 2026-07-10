; rule slug: const_default_drops_assignments
; pass: define_inner_array   (_build_body, ARRAY_VALUE branch: `return rhs.array_value_default()`)
; contract: equisat (definitional) -- but the ARRAY_VALUE handling is INCOMPLETE.
; transform: an array defined by an ARRAY_VALUE literal is replaced by the macro
;   arr__fn(i) = <default>, i.e. a CONSTANT function equal to the literal's default,
;   IGNORING the literal's assigned-values map (fnode.array_value_assigned_values_map).
; WHAT IS CHECKED (the latent soundness gap): an ARRAY_VALUE with default d and an
;   assignment k -> v (v != d) is NOT constant. Model arr as (store (const d) k v)
;   -- the semantics of such a literal -- and ask whether arr differs from its
;   default d at some index. If yes, then replacing arr[i] by d everywhere loses the
;   k->v fact and can turn a SAT assumption set (e.g. one asserting arr[k]=v) into
;   UNSAT (false PASS).
; EXPECTED: sat  (index k witnesses arr[k]=v != d). sat here == "the default-only
;   macro is NOT equivalent to the array" == unsound WHENEVER a top-level defining RHS
;   is an ARRAY_VALUE carrying a non-empty assigned map.
; REACHABILITY CAVEAT: parsing `(store (as const T d) k v)` yields ARRAY_STORE over
;   ARRAY_VALUE(default only), which takes the (correct) store branch. A bare
;   ARRAY_VALUE with a non-empty assigned map only arises if an upstream pysmt
;   transform materializes one. So this is a LATENT gap, not reachable from raw parse.
(set-logic QF_ALIA)
(declare-fun cst () (Array Int Int))   ; stand-in for (as const) with default d
(declare-fun d () Int)
(declare-fun k () Int)
(declare-fun v () Int)
(declare-fun j () Int)
; cst is the constant array with default d:
(assert (= (select cst j) d))
; arr = ARRAY_VALUE(default d, {k -> v}) modeled as store(cst,k,v):
(define-fun arr () (Array Int Int) (store cst k v))
(assert (not (= v d)))
; does arr differ from its default d somewhere?  (the info the macro drops)
(assert (not (= (select arr k) d)))
(check-sat)
