; rule slug: probe-exclude
; pass: domain_probe  (src/simplify/domain_probe.py)
; contract: equivalence (models of the whole assertion set are UNCHANGED);
;           load-bearing direction for the verifier: unsat-preserving.
;
; WHAT THE PASS DOES
;   For a "choice" variable x constrained (somewhere) by a disjunction of
;   equalities  (or (= x c1) (= x c2) ...), the pass forms a SUBSET
;   rel = { a in assertions | freevars(a) subseteq cluster }  (see
;   _cluster_assertions), builds a fresh solver over rel only, and for each
;   candidate value v probes SAT of  rel /\ (x = v).  If that probe is
;   definitively UNSAT (solver returns False, not unknown), it INJECTS the
;   literal  (not (= x v))  into the FULL script before check-sat.
;   Only confirmed-unsat probes ever inject; unknown/rlimit -> nothing.
;
; SOUNDNESS OBLIGATION (the hint: "injected constraints are actually implied")
;   The injected fact (x != v) must be entailed by the FULL assertion set Phi.
;   The pass only knows  rel /\ (x=v)  is UNSAT, where rel is a SUBSET of Phi
;   (Phi = rel /\ E, E = the dropped assertions).  By monotonicity of
;   unsatisfiability, rel subseteq Phi implies:
;       (rel /\ x=v) UNSAT  ==>  (Phi /\ x=v) UNSAT  ==>  Phi |= (x != v).
;   So the injected literal is a logical consequence of Phi, and adding it
;   leaves the model set of Phi unchanged (equivalence). Dropping assertions
;   to form rel can only make FEWER exclusions provable (incompleteness),
;   never a spurious one.  Soundness does NOT depend on the field prime; it is
;   a pure entailment/monotonicity fact, so no BabyBear variant is needed.
;
; WHAT THIS FILE CHECKS
;   The crux reduces to: rel subseteq Phi, i.e. Phi |= rel, on a concrete
;   field instance (P=97) with a genuine exclusion.  We assert Phi and the
;   negation of rel.  If that is UNSAT, then every model of Phi satisfies rel,
;   hence any value the pass excludes because it is rel-infeasible is also
;   Phi-infeasible: no spurious exclusion.
;
; EXPECTED: unsat  => rule SOUND.
;   A 'sat' model would be a point satisfying the full Phi while violating the
;   probed subset rel -- meaning the subset used for probing is NOT actually a
;   subset of the constraints, which would let the pass exclude a Phi-feasible
;   value (a false PASS). That cannot happen here.
(set-logic QF_NIA)

(declare-fun x () Int)
(declare-fun y () Int)

; --- rel: the subset the pass probes over (fully inside the cluster of x) ---
; R1: choice constraint  x in {1,2,3}
(define-fun R1 () Bool (or (= x 1) (= x 2) (= x 3)))
; R2: x^2 = 4 (mod 97)  -> x in {2, 95}; with R1 forces x=2, so x=1 and x=3
;     are genuinely excluded by rel alone (the exclusions the pass injects).
(define-fun R2 () Bool (= (mod (* x x) 97) 4))
(define-fun rel () Bool (and R1 R2))

; --- E: the assertions dropped when restricting to rel (they mention y) ---
(define-fun E1 () Bool (= (mod (+ x y) 97) 0))
(define-fun E2 () Bool (or (= y 95) (= y 0)))
(define-fun Phi () Bool (and rel E1 E2))

; Soundness lemma: Phi |= rel   <=>   (Phi /\ not rel) is UNSAT.
(assert Phi)
(assert (not rel))
(check-sat)
