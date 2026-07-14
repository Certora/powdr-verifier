; rule: rewrite-mod-drop-symbol   (rewrite_mod -- DORMANT: operators.MOD entry is
;   commented out in REWRITES.)
; source: rewrites.py rewrite_mod:
;     if modulus.is_int_constant(P) and expr.is_symbol(): return expr
; transform: Mod(x, p)  -->  x     (x a plain symbol; drops the modulus at the TERM level)
; contract: EQUIVALENCE of the integer term value (Mod appears as a subterm).
; what is checked HERE (no range on x): (mod x 7) == x   for all integers x?
; EXPECTED: sat  -- witness x=7 gives (mod 7 7)=0 != 7.  'sat' => the term rewrite
;   changes the value unless x is field-range constrained to [0,p). Conditionally sound;
;   currently disabled.
; NOTE: the constant-reduction part of rewrite_mod (reducing int constants mod p while
;   staying under Mod(.,p)) IS value-preserving and is not exercised here.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (not (= (mod x 7) x)))
(check-sat)
(get-value (x))
