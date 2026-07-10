; rule: not-ite-preserved  (_negate: if formula.is_ite(): return Not(formula))
; NNF does NOT push negation through a boolean Ite; it keeps Not(Ite(...)).
; contract: equivalence (boolean) -- trivial identity, but we confirm that
;   Not(Ite(c,t,e)) is logically Not(Ite(c,t,e)) (no unsound rewrite happens).
; This encodes the equivalent expansion to show leaving-as-Not is sound:
;   Not(Ite(c,t,e)) <=> Ite(c, Not t, Not e).
; expect UNSAT = the kept form is consistent with the semantics (sound).
(set-logic QF_UF)
(declare-const c Bool)
(declare-const t Bool)
(declare-const e Bool)
(assert (not (= (not (ite c t e)) (ite c (not t) (not e)))))
(check-sat)
