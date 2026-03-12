from __future__ import annotations

from typing import Dict, Iterable, Optional

from ...smt.utils import ARGS, And, Bool, Equals, Exists, FNode, ForAll, Implies, Int, Mod, Not, Or
from .domain import INF, IntDomain, IntInterval
from .helpers import (
    _affine,
    _ceil_div,
    _is_bool_const,
    _is_int_const,
    _is_mod_p,
    _unique_multiple_in_domain,
)


class IntervalReasoner:
    """Disjunctive interval propagation over pySMT Int formulas."""

    def __init__(self, modulus: Optional[int] = None, p: Optional[int] = None):
        if modulus is None and p is not None:
            modulus = p
        self.p = int(ARGS().field_type.value if modulus is None else modulus)
        self.env: Dict[FNode, IntDomain] = {}
        self.used_formulas: set[FNode] = set()
        self.tightened_symbols: set[FNode] = set()
        self._cache: Dict[FNode, IntDomain] = {}

    def _default(self, sym: FNode) -> IntDomain:
        # Start from full integer domain. Field bounds are learned from constraints.
        return IntDomain.top()

    def get_domain(self, sym: FNode) -> IntDomain:
        if sym in self.env:
            return self.env[sym]
        if sym.is_symbol() and sym.get_type().is_int_type():
            self.env[sym] = self._default(sym)
            return self.env[sym]
        return IntDomain.top()

    def get_interval(self, sym: FNode) -> IntInterval:
        # Backward-compatible API used by existing tests/callers.
        return self.get_domain(sym).hull()

    def _state_get(self, state: Dict[FNode, IntDomain], sym: FNode) -> IntDomain:
        if sym in state:
            return state[sym]
        if sym.is_symbol() and sym.get_type().is_int_type():
            return IntDomain.top()
        return IntDomain.top()

    def _state_set(
        self,
        state: Dict[FNode, IntDomain],
        sym: FNode,
        new_d: IntDomain,
        *,
        tightened: Optional[set[FNode]] = None,
        invalidate_global_cache: bool = False,
    ) -> bool:
        old = self._state_get(state, sym)
        merged = old.intersect(new_d)
        if merged == old:
            return False
        state[sym] = merged
        if tightened is not None:
            tightened.add(sym)
        if invalidate_global_cache:
            self._cache.clear()
        return True

    def _eval_int(self, e: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> IntDomain:
        if e in cache:
            return cache[e]

        if (c := _is_int_const(e)) is not None:
            r = IntDomain.const(c)
        elif e.is_symbol():
            r = self._state_get(state, e)
        elif e.is_plus():
            acc = IntDomain.const(0)
            for a in e.args():
                acc = acc.add(self._eval_int(a, state, cache))
            r = acc
        elif e.is_minus():
            a, b = e.args()
            r = self._eval_int(a, state, cache).sub(self._eval_int(b, state, cache))
        elif e.is_times():
            acc = IntDomain.const(1)
            for a in e.args():
                acc = acc.mul(self._eval_int(a, state, cache))
            r = acc
        elif e.is_mod():
            a, m = e.args()
            mv = _is_int_const(m)
            if mv is not None and mv > 0:
                ai = self._eval_int(a, state, cache)
                if ai.within_0_p(mv):
                    r = ai
                else:
                    r = IntDomain.from_interval(IntInterval(0, mv - 1))
            else:
                r = IntDomain.top()
        else:
            r = IntDomain.top()

        cache[e] = r
        return r

    def _eval_bool(self, f: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> Optional[bool]:
        if (bc := _is_bool_const(f)) is not None:
            return bc
        if f.is_not():
            v = self._eval_bool(f.arg(0), state, cache)
            return None if v is None else (not v)
        if f.is_and():
            vals = [self._eval_bool(a, state, cache) for a in f.args()]
            if False in vals:
                return False
            if None in vals:
                return None
            return True
        if f.is_or():
            vals = [self._eval_bool(a, state, cache) for a in f.args()]
            if True in vals:
                return True
            if None in vals:
                return None
            return False
        if f.is_implies():
            a, b = f.args()
            va = self._eval_bool(a, state, cache)
            vb = self._eval_bool(b, state, cache)
            if va is False or vb is True:
                return True
            if va is True:
                return vb
            return None
        if f.is_equals() or f.is_lt() or f.is_le():
            a, b = f.args()
            ai = self._eval_int(a, state, cache)
            bi = self._eval_int(b, state, cache)
            if f.is_equals():
                if ai.intersect(bi).is_bottom():
                    return False
                va = ai.singleton_value()
                vb = bi.singleton_value()
                if va is not None and vb is not None and va == vb:
                    return True
                return None
            ahi = ai.hull()
            bhi = bi.hull()
            if f.is_lt():
                if ahi.hi is not None and bhi.lo is not None and ahi.hi < bhi.lo:
                    return True
                if ahi.lo is not None and bhi.hi is not None and ahi.lo >= bhi.hi:
                    return False
                return None
            if ahi.hi is not None and bhi.lo is not None and ahi.hi <= bhi.lo:
                return True
            if ahi.lo is not None and bhi.hi is not None and ahi.lo > bhi.hi:
                return False
            return None
        return None

    def eval_bool(self, f: FNode) -> Optional[bool]:
        return self._eval_bool(f, self.env, self._cache)

    def _refine_affine_eq(
        self,
        a: FNode,
        b: FNode,
        state: Dict[FNode, IntDomain],
        cache: Dict[FNode, IntDomain],
    ) -> bool:
        aff_a = _affine(a)
        aff_b = _affine(b)
        if aff_a is None or aff_b is None:
            return False
        ca, ma = aff_a
        cb, mb = aff_b

        const = ca - cb
        terms = dict(ma)
        for s, c in mb.items():
            terms[s] = terms.get(s, 0) - c
            if terms[s] == 0:
                del terms[s]
        if not terms:
            return False

        changed = False
        for sym, coeff in terms.items():
            other = IntDomain.const(const)
            for t, c in terms.items():
                if t is sym:
                    continue
                other = other.add(self._eval_int(t, state, cache).scale(c))
            h = other.hull()
            if h.lo is None or h.hi is None:
                continue

            lo_num = -h.hi
            hi_num = -h.lo
            if coeff < 0:
                coeff = -coeff
                lo_num, hi_num = -hi_num, -lo_num

            lo = _ceil_div(lo_num, coeff)
            hi = hi_num // coeff
            changed |= self._state_set(state, sym, IntDomain.from_interval(IntInterval(lo, hi)))
        return changed

    def _refine_affine_ineq(
        self,
        a: FNode,
        b: FNode,
        *,
        strict: bool,
        state: Dict[FNode, IntDomain],
        cache: Dict[FNode, IntDomain],
    ) -> bool:
        aff_a = _affine(a)
        aff_b = _affine(b)
        if aff_a is None or aff_b is None:
            return False
        ca, ma = aff_a
        cb, mb = aff_b

        const = ca - cb
        terms = dict(ma)
        for s, c in mb.items():
            terms[s] = terms.get(s, 0) - c
            if terms[s] == 0:
                del terms[s]
        if not terms:
            return False

        target_hi = -1 if strict else 0
        changed = False
        for sym, coeff in terms.items():
            rest = IntDomain.const(const)
            for t, c in terms.items():
                if t is sym:
                    continue
                rest = rest.add(self._eval_int(t, state, cache).scale(c))
            h = rest.hull()

            if coeff > 0:
                if h.lo is None:
                    continue
                rhs = target_hi - h.lo
                hi = rhs // coeff
                changed |= self._state_set(state, sym, IntDomain.from_interval(IntInterval(INF, hi)))
            elif coeff < 0:
                if h.hi is None:
                    continue
                den = -coeff
                num = h.hi - target_hi
                lo = _ceil_div(num, den)
                changed |= self._state_set(state, sym, IntDomain.from_interval(IntInterval(lo, INF)))
        return changed

    def _refine_from_ineq(self, f: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> bool:
        if not (f.is_lt() or f.is_le()):
            return False
        a, b = f.args()
        strict = f.is_lt()
        am = _is_mod_p(a, self.p)
        bm = _is_mod_p(b, self.p)
        if am is not None:
            a = am
        if bm is not None:
            b = bm

        changed = False
        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            ub = c - 1 if strict else c
            changed |= self._state_set(state, a, IntDomain.from_interval(IntInterval(INF, ub)))
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            lb = c + 1 if strict else c
            changed |= self._state_set(state, b, IntDomain.from_interval(IntInterval(lb, INF)))
        changed |= self._refine_affine_ineq(a, b, strict=strict, state=state, cache=cache)
        return changed

    def _refine_from_eq(self, f: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> bool:
        if not f.is_equals():
            return False
        a, b = f.args()
        changed = False
        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            changed |= self._state_set(state, a, IntDomain.const(c))
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            changed |= self._state_set(state, b, IntDomain.const(c))

        # Mod(sym,p) == c and sym already canonical -> sym == c
        if (x := _is_mod_p(a, self.p)) is not None and (c := _is_int_const(b)) is not None:
            if self._eval_int(x, state, cache).within_0_p(self.p) and x.is_symbol():
                changed |= self._state_set(state, x, IntDomain.const(c))
        if (x := _is_mod_p(b, self.p)) is not None and (c := _is_int_const(a)) is not None:
            if self._eval_int(x, state, cache).within_0_p(self.p) and x.is_symbol():
                changed |= self._state_set(state, x, IntDomain.const(c))

        changed |= self._refine_affine_eq(a, b, state, cache)
        return changed

    def _refine_from_or_equalities(self, f: FNode, state: Dict[FNode, IntDomain]) -> bool:
        if not f.is_or():
            return False
        sym = None
        vals: list[int] = []
        for d in f.args():
            if not d.is_equals():
                return False
            a, b = d.args()
            if a.is_symbol() and (c := _is_int_const(b)) is not None:
                cur_sym = a
            elif b.is_symbol() and (c := _is_int_const(a)) is not None:
                cur_sym = b
            else:
                return False
            if sym is None:
                sym = cur_sym
            elif sym != cur_sym:
                return False
            vals.append(c)
        if sym is None or not vals:
            return False
        dom = IntDomain.from_intervals(IntInterval.const(v) for v in vals)
        return self._state_set(state, sym, dom)

    def _refine_from_mod_zero(self, f: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> bool:
        if not f.is_equals():
            return False
        a, b = f.args()
        mod_expr = None
        if a.is_mod() and _is_int_const(b) == 0:
            mod_expr = a
        elif b.is_mod() and _is_int_const(a) == 0:
            mod_expr = b
        if mod_expr is None:
            return False

        inner, modulus = mod_expr.args()
        p = _is_int_const(modulus)
        if p is None or p <= 0:
            return False

        changed = False
        inner_d = self._eval_int(inner, state, cache)
        uniq = _unique_multiple_in_domain(inner_d, p)
        if uniq is not None:
            changed |= self._refine_affine_eq(inner, Int(uniq), state, cache)

        # Prime-field product reasoning:
        #   (u1 * ... * uk) == 0 (mod p)  =>  ui == 0 (mod p) for some i.
        # For affine unit-coefficient factors over canonical symbol ranges, each
        # factor gives a concrete residue candidate.
        if inner.is_times():
            candidates: Dict[FNode, set[int]] = {}
            for factor in inner.args():
                aff = _affine(factor)
                if aff is None:
                    continue
                c0, terms = aff
                if len(terms) != 1:
                    continue
                sym, coeff = next(iter(terms.items()))
                if coeff not in (1, -1):
                    continue
                if not sym.is_symbol() or not sym.get_type().is_int_type():
                    continue
                sym_dom = self._state_get(state, sym)
                if not sym_dom.within_0_p(p):
                    continue
                if coeff == 1:
                    cand = (-c0) % p
                else:
                    cand = c0 % p
                candidates.setdefault(sym, set()).add(cand)

            for sym, vals in candidates.items():
                if not vals:
                    continue
                dom = IntDomain.from_intervals(IntInterval.const(v) for v in sorted(vals))
                changed |= self._state_set(state, sym, dom)

        return changed

    def _refine_atom(self, atom: FNode, state: Dict[FNode, IntDomain], cache: Dict[FNode, IntDomain]) -> bool:
        changed = False
        changed |= self._refine_from_ineq(atom, state, cache)
        changed |= self._refine_from_eq(atom, state, cache)
        changed |= self._refine_from_or_equalities(atom, state)
        changed |= self._refine_from_mod_zero(atom, state, cache)
        return changed

    def _state_inconsistent(self, state: Dict[FNode, IntDomain]) -> bool:
        return any(dom.is_bottom() for dom in state.values())

    def _meet_states_inplace(
        self,
        target: Dict[FNode, IntDomain],
        source: Dict[FNode, IntDomain],
        *,
        tightened: Optional[set[FNode]] = None,
        invalidate_global_cache: bool = False,
    ) -> bool:
        changed = False
        for sym, d in source.items():
            changed |= self._state_set(
                target,
                sym,
                d,
                tightened=tightened,
                invalidate_global_cache=invalidate_global_cache,
            )
        return changed

    def _propagate_atom_fixpoint(self, atom: FNode, base: Dict[FNode, IntDomain]) -> Dict[FNode, IntDomain]:
        state = dict(base)
        for _ in range(8):
            cache: Dict[FNode, IntDomain] = {}
            changed = self._refine_atom(atom, state, cache)
            if not changed or self._state_inconsistent(state):
                break
        return state

    def _propagate_not(self, f: FNode, base: Dict[FNode, IntDomain]) -> Dict[FNode, IntDomain]:
        if f.is_not():
            return self._propagate_formula(f.arg(0), base)
        if f.is_and():
            return self._propagate_formula(Or(*[Not(a) for a in f.args()]), base)
        if f.is_or():
            return self._propagate_formula(And(*[Not(a) for a in f.args()]), base)
        if f.is_implies():
            a, b = f.args()
            return self._propagate_formula(And(a, Not(b)), base)
        if f.is_lt():
            a, b = f.args()
            return self._propagate_formula(b <= a, base)
        if f.is_le():
            a, b = f.args()
            return self._propagate_formula(b < a, base)
        return dict(base)

    def _propagate_formula(self, f: FNode, base: Dict[FNode, IntDomain]) -> Dict[FNode, IntDomain]:
        if f.is_and():
            state = dict(base)
            for _ in range(8):
                changed = False
                for a in f.args():
                    child = self._propagate_formula(a, state)
                    changed |= self._meet_states_inplace(state, child)
                    if self._state_inconsistent(state):
                        return state
                if not changed:
                    break
            return state

        if f.is_or():
            branch_states = [self._propagate_formula(a, dict(base)) for a in f.args()]
            consistent = [s for s in branch_states if not self._state_inconsistent(s)]
            if not consistent:
                out = dict(base)
                int_vars = [v for v in f.get_free_variables() if v.get_type().is_int_type()]
                if int_vars:
                    out[int_vars[0]] = IntDomain.bottom()
                return out

            out = dict(base)
            all_syms = set().union(*[set(s.keys()) for s in consistent])
            for sym in all_syms:
                joined = IntDomain.bottom()
                for st in consistent:
                    joined = joined.union(st.get(sym, self._state_get(base, sym)))
                out[sym] = self._state_get(base, sym).intersect(joined)
            return out

        if f.is_implies():
            a, b = f.args()
            return self._propagate_formula(Or(Not(a), b), base)

        if f.is_not():
            return self._propagate_not(f.arg(0), base)

        if f.is_exists() or f.is_forall():
            # Quantifiers are solved in a separate pass after root fixed point.
            return dict(base)

        return self._propagate_atom_fixpoint(f, base)

    def assume_all(self, assumptions: Iterable[FNode], max_iters: int = 10) -> None:
        work = list(assumptions)
        for _ in range(max_iters):
            changed = False
            for f in work:
                normalized = self.simplify(f, prune=False, inject_quantifier_bounds=False)
                local_state = self._propagate_formula(normalized, dict(self.env))
                local_changed = self._meet_states_inplace(
                    self.env,
                    local_state,
                    tightened=self.tightened_symbols,
                    invalidate_global_cache=True,
                )
                if local_changed:
                    self.used_formulas.add(f)
                changed |= local_changed
            if not changed:
                break

    def must_retain_formula(self, f: FNode) -> bool:
        """Return True for constraints that must not be pruned away."""
        if f in self.used_formulas:
            return True
        if f.is_and():
            return any(self.must_retain_formula(a) for a in f.args())
        if not (f.is_le() or f.is_lt() or f.is_equals()):
            return False

        a, b = f.args()
        ac = _is_int_const(a)
        bc = _is_int_const(b)

        if f.is_le():
            if ac == 0 and b.is_symbol():
                return True
            if bc in (self.p, self.p - 1) and a.is_symbol():
                return True
        elif f.is_lt():
            if bc in (self.p, self.p + 1) and a.is_symbol():
                return True
        else:
            if ac in (0, self.p) and b.is_symbol():
                return True
            if bc in (0, self.p) and a.is_symbol():
                return True
        return False

    def _domain_constraint(self, sym: FNode, dom: IntDomain) -> Optional[FNode]:
        if dom.is_bottom():
            return Bool(False)
        disjuncts: list[FNode] = []
        for iv in dom.parts:
            if iv.lo is None and iv.hi is None:
                return None
            if iv.lo is not None and iv.hi is not None and iv.lo == iv.hi:
                disjuncts.append(Equals(sym, Int(iv.lo)))
                continue
            parts = []
            if iv.lo is not None:
                parts.append(Int(iv.lo) <= sym)
            if iv.hi is not None:
                parts.append(sym <= Int(iv.hi))
            if not parts:
                continue
            disjuncts.append(parts[0] if len(parts) == 1 else And(*parts))
        if not disjuncts:
            return None
        return disjuncts[0] if len(disjuncts) == 1 else Or(*disjuncts)

    def derived_range_constraints(self, *, only_tightened: bool = True) -> list[FNode]:
        symbols = self.tightened_symbols if only_tightened else set(self.env.keys())
        out: list[FNode] = []
        for sym in sorted(symbols, key=str):
            dom = self.get_domain(sym)
            c = self._domain_constraint(sym, dom)
            if c is not None:
                out.append(c)
        return out

    def inject_root_bounds(self, f: FNode, *, only_tightened: bool = True) -> FNode:
        """Conjoin inferred global bounds for integer vars appearing in ``f``."""
        if not f.get_type().is_bool_type():
            return f
        tracked = self.tightened_symbols if only_tightened else set(self.env.keys())
        free_int_vars = {v for v in f.get_free_variables() if v.get_type().is_int_type()}
        symbols = free_int_vars if free_int_vars else tracked
        bounds: list[FNode] = []
        for sym in sorted(symbols, key=str):
            if sym not in tracked:
                continue
            c = self._domain_constraint(sym, self.get_domain(sym))
            if c is not None:
                bounds.append(c)
        if not bounds:
            return f
        return And(*(bounds + [f])).simplify()

    def _inject_quantifier_bounds(self, n: FNode, inherited: Dict[FNode, IntDomain], max_iters: int) -> FNode:
        if n.is_forall() or n.is_exists():
            qvars = list(n.quantifier_vars())
            body = n.arg(0)
            body_int_vars = {v for v in body.get_free_variables() if v.get_type().is_int_type()}
            shadowed_names = {q.symbol_name() for q in qvars}

            seed = {
                v: inherited[v]
                for v in body_int_vars
                if v in inherited and v.symbol_name() not in shadowed_names
            }

            local = IntervalReasoner(modulus=self.p)
            local.env = dict(seed)
            local.assume_all([body], max_iters=max_iters)

            rewritten_body = self._inject_quantifier_bounds(body, local.env, max_iters)

            outer_bounds: list[FNode] = []
            local_bounds: list[FNode] = []
            for sym in sorted(body_int_vars, key=str):
                if sym in inherited and sym.symbol_name() not in shadowed_names:
                    c_outer = self._domain_constraint(sym, inherited[sym])
                    if c_outer is not None:
                        outer_bounds.append(c_outer)
                c_local = self._domain_constraint(sym, local.get_domain(sym))
                if c_local is not None:
                    local_bounds.append(c_local)

            outer_guard = None if not outer_bounds else (outer_bounds[0] if len(outer_bounds) == 1 else And(*outer_bounds))
            local_guard = None if not local_bounds else (local_bounds[0] if len(local_bounds) == 1 else And(*local_bounds))

            body_with_local = rewritten_body if local_guard is None else And(local_guard, rewritten_body)
            if n.is_exists():
                injected_body = body_with_local
            else:
                injected_body = body_with_local if outer_guard is None else Implies(outer_guard, body_with_local)

            return Exists(qvars, injected_body) if n.is_exists() else ForAll(qvars, injected_body)

        if n.is_and():
            rewritten_args = [self._inject_quantifier_bounds(a, inherited, max_iters) for a in n.args()]

            # Local conjunction reasoning: if the conjunction itself forces
            # singleton integer symbols, make these facts explicit.
            # This is sound regardless of polarity because we only add facts
            # implied by the conjunction itself (no inherited seeding here).
            local = IntervalReasoner(modulus=self.p)
            local.assume_all(rewritten_args, max_iters=max_iters)
            present = set(rewritten_args)
            for sym in sorted({v for v in n.get_free_variables() if v.get_type().is_int_type()}, key=str):
                val = local.get_domain(sym).singleton_value()
                if val is None:
                    continue
                eq = Equals(sym, Int(val))
                if eq not in present:
                    rewritten_args.append(eq)
                    present.add(eq)

            # Substitute singleton integer symbols across siblings so inferred
            # equalities are immediately exploited by remaining constraints.
            substitutions = {
                sym: Int(val)
                for sym in {v for v in n.get_free_variables() if v.get_type().is_int_type()}
                if (val := local.get_domain(sym).singleton_value()) is not None
            }
            if substitutions:
                rewritten_args = [a.substitute(substitutions).simplify() for a in rewritten_args]

            # Re-simplify in the local fixed-point environment so newly
            # inferred singleton equalities prune/eliminate sibling constraints.
            local.assume_all(rewritten_args, max_iters=max_iters)
            return local.simplify(And(*rewritten_args), prune=True, inject_quantifier_bounds=False)
        if n.is_or():
            return Or(*[self._inject_quantifier_bounds(a, inherited, max_iters) for a in n.args()])
        if n.is_implies():
            a, b = n.args()
            return Implies(
                self._inject_quantifier_bounds(a, inherited, max_iters),
                self._inject_quantifier_bounds(b, inherited, max_iters),
            )
        if n.is_not():
            return Not(self._inject_quantifier_bounds(n.arg(0), inherited, max_iters))
        return n

    def inject_quantifier_bounds(self, f: FNode, *, max_iters: int = 6) -> FNode:
        return self._inject_quantifier_bounds(f, self.env, max_iters)

    def simplify(
        self,
        f: FNode,
        *,
        prune: bool = True,
        freeze: Optional[set[FNode]] = None,
        inject_quantifier_bounds: bool = False,
    ) -> FNode:
        if freeze and f in freeze:
            out = f
            return self.inject_quantifier_bounds(out) if inject_quantifier_bounds else out
        memo: Dict[FNode, FNode] = {}

        def go(n: FNode) -> FNode:
            if n in memo:
                return memo[n]
            if freeze and n in freeze:
                memo[n] = n
                return n

            if prune:
                vb = self.eval_bool(n)
                if vb is True:
                    memo[n] = Bool(True)
                    return memo[n]
                if vb is False:
                    memo[n] = Bool(False)
                    return memo[n]

            if n.is_and():
                args = [go(a) for a in n.args()]
                if prune:
                    out = []
                    for a in args:
                        if _is_bool_const(a) is True:
                            continue
                        if _is_bool_const(a) is False:
                            memo[n] = Bool(False)
                            return memo[n]
                        out.append(a)
                    memo[n] = Bool(True) if not out else And(*out)
                    return memo[n]
                memo[n] = And(*args)
                return memo[n]

            if n.is_or():
                args = [go(a) for a in n.args()]
                if prune:
                    out = []
                    for a in args:
                        if _is_bool_const(a) is False:
                            continue
                        if _is_bool_const(a) is True:
                            memo[n] = Bool(True)
                            return memo[n]
                        out.append(a)
                    memo[n] = Bool(False) if not out else Or(*out)
                    return memo[n]
                memo[n] = Or(*args)
                return memo[n]

            if n.is_implies():
                a, b = n.args()
                memo[n] = Implies(go(a), go(b))
                return memo[n]

            if n.is_not():
                memo[n] = Not(go(n.arg(0)))
                return memo[n]

            if n.is_mod():
                a, m = n.args()
                mv = _is_int_const(m)
                if mv is not None and self._eval_int(a, self.env, self._cache).within_0_p(mv):
                    memo[n] = a
                    return memo[n]
                memo[n] = Mod(go(a), go(m))
                return memo[n]

            if n.is_equals():
                a, b = n.args()
                if (x := _is_mod_p(a, self.p)) is not None and _is_int_const(b) == 0:
                    x_dom = self._eval_int(x, self.env, self._cache)
                    if x_dom.within_open_pm_p(self.p):
                        memo[n] = Equals(x, Int(0))
                        return memo[n]
                    if (uniq := _unique_multiple_in_domain(x_dom, self.p)) is not None:
                        memo[n] = Equals(x, Int(uniq))
                        return memo[n]
                if (x := _is_mod_p(b, self.p)) is not None and _is_int_const(a) == 0:
                    x_dom = self._eval_int(x, self.env, self._cache)
                    if x_dom.within_open_pm_p(self.p):
                        memo[n] = Equals(x, Int(0))
                        return memo[n]
                    if (uniq := _unique_multiple_in_domain(x_dom, self.p)) is not None:
                        memo[n] = Equals(x, Int(uniq))
                        return memo[n]
                memo[n] = Equals(go(a), go(b))
                return memo[n]

            memo[n] = n
            return n

        out = go(f)
        return self.inject_quantifier_bounds(out) if inject_quantifier_bounds else out
