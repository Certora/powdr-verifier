"""Constraint-driven propagation of per-variable integer intervals (two variants)."""
from __future__ import annotations

import logging
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

logger = logging.getLogger(__name__)


def _fmt_interval(iv: IntInterval) -> str:
    """Human-readable ``[lo,hi]`` for logging."""
    lo = "-inf" if iv.lo is None else str(iv.lo)
    hi = "+inf" if iv.hi is None else str(iv.hi)
    return f"[{lo},{hi}]"


def _fmt_domain(dom: IntDomain) -> str:
    """Serialize ``IntDomain`` as union of interval strings."""
    if dom.is_bottom():
        return "<empty>"
    return " | ".join(_fmt_interval(iv) for iv in dom.parts)


def _fmt_formula(f: FNode, max_len: int = 200) -> str:
    """Truncate ``str(f)`` for debug logs."""
    s = str(f)
    if len(s) <= max_len:
        return s
    return s[: max_len - 3] + "..."


def _subformula_ctx(parent: Optional[str], label: str) -> str:
    """Build a path label for logging propagation under a subformula."""
    if parent:
        return f"{parent}/{label}"
    return label


def _domain_is_full_field_hull(dom: IntDomain, p: int) -> bool:
    """True if ``dom`` is the whole-field hull [0, p-1] or [0, p] (single interval, lo fixed at 0)."""
    full = IntDomain.from_interval(IntInterval(0, p-1))
    return dom.intersect(full) == full


class IntervalReasoner:
    """Disjunctive interval propagation over pySMT Int formulas."""

    def __init__(
        self,
        modulus: Optional[int] = None,
        p: Optional[int] = None,
        *,
        log_interval_shrinks: bool = False,
    ):
        """``modulus``/``p``: field prime; default from ``ARGS().field_type``."""
        if modulus is None and p is not None:
            modulus = p
        self.p = int(ARGS().field_type.value if modulus is None else modulus)
        self.env: Dict[FNode, IntDomain] = {}
        self.used_formulas: set[FNode] = set()
        self.tightened_symbols: set[FNode] = set()
        self.log_interval_shrinks = log_interval_shrinks

    def _should_log_shrinks(self) -> bool:
        """True when interval shrink logging is enabled."""
        return self.log_interval_shrinks or logger.isEnabledFor(logging.INFO)

    def _default(self, sym: FNode) -> IntDomain:
        """Initial domain for a symbol before any constraints."""
        # Start from full integer domain. Field bounds are learned from constraints.
        return IntDomain.top()

    def get_domain(self, sym: FNode) -> IntDomain:
        """Return current ``IntDomain`` for ``sym``, or ``top`` if unseen."""
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
        step: Optional[str] = None,
        formula_ctx: Optional[str] = None,
    ) -> bool:
        old = self._state_get(state, sym)
        merged = old.intersect(new_d)
        if merged == old:
            return False
        if self._should_log_shrinks() and not _domain_is_full_field_hull(old, self.p) and not _domain_is_full_field_hull(merged, self.p):
            msg = f"interval shrink: {sym!s}: {_fmt_domain(old)} intersect {_fmt_domain(new_d)} -> {_fmt_domain(merged)}"
            if step:
                msg = f"[{step}] {msg}"
            if formula_ctx:
                msg = f"[ctx: {formula_ctx}] {msg}"
            logger.info(msg)
        state[sym] = merged
        if tightened is not None:
            tightened.add(sym)
        return True

    def _eval_int(self, e: FNode, state: Dict[FNode, IntDomain]) -> IntDomain:
        if (c := _is_int_const(e)) is not None:
            r = IntDomain.const(c)
        elif e.is_symbol():
            r = self._state_get(state, e)
        elif e.is_plus():
            acc = IntDomain.const(0)
            for a in e.args():
                acc = acc.add(self._eval_int(a, state))
            r = acc
        elif e.is_minus():
            a, b = e.args()
            r = self._eval_int(a, state).sub(self._eval_int(b, state))
        elif e.is_times():
            acc = IntDomain.const(1)
            for a in e.args():
                acc = acc.mul(self._eval_int(a, state))
            r = acc
        elif e.is_mod():
            a, m = e.args()
            mv = _is_int_const(m)
            if mv is not None and mv > 0:
                ai = self._eval_int(a, state)
                if ai.within_0_p(mv):
                    r = ai
                else:
                    r = IntDomain.from_interval(IntInterval(0, mv - 1))
            else:
                r = IntDomain.top()
        else:
            r = IntDomain.top()

        return r

    def _eval_bool(self, f: FNode, state: Dict[FNode, IntDomain]) -> Optional[bool]:
        if (bc := _is_bool_const(f)) is not None:
            return bc
        if f.is_not():
            v = self._eval_bool(f.arg(0), state)
            return None if v is None else (not v)
        if f.is_and():
            vals = [self._eval_bool(a, state) for a in f.args()]
            if False in vals:
                return False
            if None in vals:
                return None
            return True
        if f.is_or():
            vals = [self._eval_bool(a, state) for a in f.args()]
            if True in vals:
                return True
            if None in vals:
                # If all disjuncts are negations, check whether the conjunction
                # of their inner formulas is inconsistent. In that case:
                #   (not a1) or ... or (not an)  is a tautology.
                not_args = [a.arg(0) for a in f.args() if a.is_not()]
                if len(not_args) == len(f.args()) and len(not_args) >= 2:
                    local = IntervalReasoner(modulus=self.p, log_interval_shrinks=self.log_interval_shrinks)
                    local.env = dict(state)
                    local.assume_all(
                        not_args,
                        max_iters=6,
                        context=f"eval_bool Or-not-tautology {_fmt_formula(f, max_len=120)}",
                    )
                    if local._state_inconsistent(local.env):
                        return True
                return None
            return False
        if f.is_implies():
            a, b = f.args()
            va = self._eval_bool(a, state)
            vb = self._eval_bool(b, state)
            if va is False or vb is True:
                return True
            if va is True:
                return vb
            return None
        if f.is_equals() or f.is_lt() or f.is_le():
            a, b = f.args()
            ai = self._eval_int(a, state)
            bi = self._eval_int(b, state)
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
        return self._eval_bool(f, self.env)

    def _refine_affine_eq(
        self,
        a: FNode,
        b: FNode,
        state: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
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
                other = other.add(self._eval_int(t, state).scale(c))
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
            changed |= self._state_set(
                state,
                sym,
                IntDomain.from_interval(IntInterval(lo, hi)),
                step="affine_eq",
                formula_ctx=formula_ctx,
            )
        return changed

    def _refine_affine_ineq(
        self,
        a: FNode,
        b: FNode,
        *,
        strict: bool,
        state: Dict[FNode, IntDomain],
        formula_ctx: Optional[str] = None,
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
                rest = rest.add(self._eval_int(t, state).scale(c))
            h = rest.hull()

            if coeff > 0:
                if h.lo is None:
                    continue
                rhs = target_hi - h.lo
                hi = rhs // coeff
                changed |= self._state_set(
                    state,
                    sym,
                    IntDomain.from_interval(IntInterval(INF, hi)),
                    step="affine_ineq_pos",
                    formula_ctx=formula_ctx,
                )
            elif coeff < 0:
                # Dividing coeff*sym <= target_hi - rest by coeff < 0 flips the
                # relation to sym >= (rest - target_hi)/den (den = -coeff). A lower
                # bound valid for every feasible rest must use the SMALLEST rest,
                # i.e. rest.lo -- using rest.hi over-tightens and drops models
                # (a false PASS) whenever rest is not a singleton. The coeff > 0
                # branch above symmetrically (and correctly) uses h.lo.
                if h.lo is None:
                    continue
                den = -coeff
                num = h.lo - target_hi
                lo = _ceil_div(num, den)
                changed |= self._state_set(
                    state,
                    sym,
                    IntDomain.from_interval(IntInterval(lo, INF)),
                    step="affine_ineq_neg",
                    formula_ctx=formula_ctx,
                )
        return changed

    def _mod_ineq_is_tautology(self, f: FNode) -> bool:
        """True if ``f`` holds for every value of ``(mod E p)`` in ``[0, p-1]``."""
        if not (f.is_lt() or f.is_le()):
            return False
        a, b = f.args()
        strict = f.is_lt()
        am = _is_mod_p(a, self.p)
        bm = _is_mod_p(b, self.p)
        p = self.p
        if bm is not None:
            if f.is_le() and _is_int_const(a) == 0:
                return True
            if strict and (ca := _is_int_const(a)) is not None and ca < 0:
                return True
        if am is not None:
            if (cb := _is_int_const(b)) is not None:
                if not strict and cb >= p - 1:
                    return True
                if strict and cb >= p:
                    return True
        return False

    def _refine_from_ineq(
        self,
        f: FNode,
        state: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> bool:
        if not (f.is_lt() or f.is_le()):
            return False
        if self._mod_ineq_is_tautology(f):
            return False
        a_orig, b_orig = f.args()
        strict = f.is_lt()
        am = _is_mod_p(a_orig, self.p)
        bm = _is_mod_p(b_orig, self.p)
        unwrap_a = am is not None and self._eval_int(am, state).within_0_p(self.p)
        unwrap_b = bm is not None and self._eval_int(bm, state).within_0_p(self.p)
        skip_affine = (am is not None and not unwrap_a) or (bm is not None and not unwrap_b)
        a, b = a_orig, b_orig
        if unwrap_a:
            a = am
        if unwrap_b:
            b = bm

        changed = False
        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            ub = c - 1 if strict else c
            changed |= self._state_set(
                state,
                a,
                IntDomain.from_interval(IntInterval(INF, ub)),
                step="ineq_sym_upper",
                formula_ctx=formula_ctx,
            )
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            lb = c + 1 if strict else c
            changed |= self._state_set(
                state,
                b,
                IntDomain.from_interval(IntInterval(lb, INF)),
                step="ineq_sym_lower",
                formula_ctx=formula_ctx,
            )
        if not skip_affine:
            changed |= self._refine_affine_ineq(
                a, b, strict=strict, state=state, formula_ctx=formula_ctx
            )
        return changed

    def _refine_from_eq(
        self,
        f: FNode,
        state: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> bool:
        if not f.is_equals():
            return False
        a, b = f.args()
        changed = False
        if a.is_symbol() and (c := _is_int_const(b)) is not None:
            changed |= self._state_set(
                state, a, IntDomain.const(c), step="eq_const", formula_ctx=formula_ctx
            )
        if b.is_symbol() and (c := _is_int_const(a)) is not None:
            changed |= self._state_set(
                state, b, IntDomain.const(c), step="eq_const", formula_ctx=formula_ctx
            )

        # Mod(sym,p) == c and sym already canonical -> sym == c
        if (x := _is_mod_p(a, self.p)) is not None and (c := _is_int_const(b)) is not None:
            if self._eval_int(x, state).within_0_p(self.p) and x.is_symbol():
                changed |= self._state_set(
                    state, x, IntDomain.const(c), step="mod_eq_const", formula_ctx=formula_ctx
                )
        if (x := _is_mod_p(b, self.p)) is not None and (c := _is_int_const(a)) is not None:
            if self._eval_int(x, state).within_0_p(self.p) and x.is_symbol():
                changed |= self._state_set(
                    state, x, IntDomain.const(c), step="mod_eq_const", formula_ctx=formula_ctx
                )

        changed |= self._refine_affine_eq(a, b, state, formula_ctx=formula_ctx)
        return changed

    def _refine_from_or_equalities(
        self, f: FNode, state: Dict[FNode, IntDomain], *, formula_ctx: Optional[str] = None
    ) -> bool:
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
        return self._state_set(state, sym, dom, step="or_equalities", formula_ctx=formula_ctx)

    def _refine_from_mod_zero(
        self,
        f: FNode,
        state: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> bool:
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
        inner_d = self._eval_int(inner, state)
        uniq = _unique_multiple_in_domain(inner_d, p)
        if uniq is not None:
            changed |= self._refine_affine_eq(
                inner, Int(uniq), state, formula_ctx=formula_ctx
            )

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
                logger.debug(f"refine_from_mod_zero: {f} -> {dom}")
                changed |= self._state_set(
                    state, sym, dom, step="mod_zero_product", formula_ctx=formula_ctx
                )

        return changed

    def _refine_atom(
        self,
        atom: FNode,
        state: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> bool:
        changed = False
        changed |= self._refine_from_ineq(atom, state, formula_ctx=formula_ctx)
        changed |= self._refine_from_eq(atom, state, formula_ctx=formula_ctx)
        changed |= self._refine_from_or_equalities(atom, state, formula_ctx=formula_ctx)
        changed |= self._refine_from_mod_zero(atom, state, formula_ctx=formula_ctx)
        return changed

    def _state_inconsistent(self, state: Dict[FNode, IntDomain]) -> bool:
        return any(dom.is_bottom() for dom in state.values())

    def _meet_states_inplace(
        self,
        target: Dict[FNode, IntDomain],
        source: Dict[FNode, IntDomain],
        *,
        tightened: Optional[set[FNode]] = None,
        step: str = "meet",
        formula_ctx: Optional[str] = None,
    ) -> bool:
        changed = False
        for sym, d in source.items():
            changed |= self._state_set(
                target,
                sym,
                d,
                tightened=tightened,
                step=step,
                formula_ctx=formula_ctx,
            )
        return changed

    def _propagate_atom_fixpoint(
        self,
        atom: FNode,
        base: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> Dict[FNode, IntDomain]:
        state = dict(base)
        for r in range(8):
            changed = self._refine_atom(atom, state, formula_ctx=formula_ctx)
            if logger.isEnabledFor(logging.DEBUG) and changed:
                logger.debug(
                    "intervals: atom fixpoint round %d/8 changed state (ctx=%s) for %s",
                    r + 1,
                    formula_ctx or "?",
                    _fmt_formula(atom),
                )
            if not changed or self._state_inconsistent(state):
                break
        return state

    def _propagate_not(
        self,
        f: FNode,
        base: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> Dict[FNode, IntDomain]:
        nctx = _subformula_ctx(formula_ctx, "Not")
        if f.is_not():
            return self._propagate_formula(f.arg(0), base, formula_ctx=nctx)
        if f.is_and():
            return self._propagate_formula(
                Or(*[Not(a) for a in f.args()]),
                base,
                formula_ctx=_subformula_ctx(nctx, "Demorgan-And"),
            )
        if f.is_or():
            return self._propagate_formula(
                And(*[Not(a) for a in f.args()]),
                base,
                formula_ctx=_subformula_ctx(nctx, "Demorgan-Or"),
            )
        if f.is_implies():
            a, b = f.args()
            return self._propagate_formula(
                And(a, Not(b)), base, formula_ctx=_subformula_ctx(nctx, "Not-implies")
            )
        if f.is_lt():
            a, b = f.args()
            return self._propagate_formula(
                b <= a, base, formula_ctx=_subformula_ctx(nctx, "Not-lt")
            )
        if f.is_le():
            a, b = f.args()
            return self._propagate_formula(
                b < a, base, formula_ctx=_subformula_ctx(nctx, "Not-le")
            )
        return dict(base)

    def _propagate_formula(
        self,
        f: FNode,
        base: Dict[FNode, IntDomain],
        *,
        formula_ctx: Optional[str] = None,
    ) -> Dict[FNode, IntDomain]:
        if f.is_and():
            state = dict(base)
            for _ in range(8):
                changed = False
                for i, a in enumerate(f.args()):
                    child_ctx = _subformula_ctx(formula_ctx, f"And[{i}]")
                    child = self._propagate_formula(a, state, formula_ctx=child_ctx)
                    changed |= self._meet_states_inplace(
                        state,
                        child,
                        step="and_propagate",
                        formula_ctx=child_ctx,
                    )
                    if self._state_inconsistent(state):
                        return state
                if not changed:
                    break
            return state

        if f.is_or():
            branch_states = [
                self._propagate_formula(
                    a, dict(base), formula_ctx=_subformula_ctx(formula_ctx, f"Or[{i}]")
                )
                for i, a in enumerate(f.args())
            ]
            consistent = [s for s in branch_states if not self._state_inconsistent(s)]
            if not consistent:
                out = dict(base)
                int_vars = [v for v in f.get_free_variables() if v.get_type().is_int_type()]
                if int_vars:
                    self._state_set(
                        out,
                        int_vars[0],
                        IntDomain.bottom(),
                        step="or_all_inconsistent",
                        formula_ctx=_subformula_ctx(formula_ctx, "Or[bottom]"),
                    )
                return out

            out = dict(base)
            join_ctx = _subformula_ctx(formula_ctx, "Or[join]")
            all_syms = set().union(*[set(s.keys()) for s in consistent])
            for sym in all_syms:
                joined = IntDomain.bottom()
                for st in consistent:
                    joined = joined.union(st.get(sym, self._state_get(base, sym)))
                self._state_set(out, sym, joined, step="or_join", formula_ctx=join_ctx)
            return out

        if f.is_implies():
            a, b = f.args()
            return self._propagate_formula(
                Or(Not(a), b), base, formula_ctx=_subformula_ctx(formula_ctx, "Implies")
            )

        if f.is_not():
            return self._propagate_not(f.arg(0), base, formula_ctx=formula_ctx)

        if f.is_exists() or f.is_forall():
            # Quantifiers are solved in a separate pass after root fixed point.
            return dict(base)

        return self._propagate_atom_fixpoint(f, base, formula_ctx=formula_ctx)

    def assume_all(
        self,
        assumptions: Iterable[FNode],
        max_iters: int = 10,
        *,
        context: Optional[str] = None,
    ) -> None:
        work = list(assumptions)
        ctx_root = context or "global"
        if logger.isEnabledFor(logging.INFO):
            logger.info(
                "intervals: assume_all starting [context=%s] (%d assertions, max_iters=%d)",
                ctx_root,
                len(work),
                max_iters,
            )
        rounds_run = 0
        for round_idx in range(max_iters):
            rounds_run = round_idx + 1
            changed = False
            for fi, f in enumerate(work):
                sub_ctx = _subformula_ctx(ctx_root, f"r{round_idx + 1}a{fi + 1}/{len(work)}")
                normalized = self.simplify(f, prune=False, inject_quantifier_bounds=False)
                if logger.isEnabledFor(logging.INFO):
                    logger.info(
                        "intervals: propagating [context=%s] %s",
                        sub_ctx,
                        _fmt_formula(normalized),
                    )
                local_state = self._propagate_formula(
                    normalized, dict(self.env), formula_ctx=sub_ctx
                )
                local_changed = self._meet_states_inplace(
                    self.env,
                    local_state,
                    tightened=self.tightened_symbols,
                    step="assume",
                    formula_ctx=sub_ctx,
                )
                if local_changed:
                    self.used_formulas.add(f)
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug(
                            "intervals: outer round %d: assertion %d/%d changed env: %s",
                            rounds_run,
                            fi + 1,
                            len(work),
                            _fmt_formula(normalized),
                        )
                changed |= local_changed
            if not changed:
                break
        if logger.isEnabledFor(logging.INFO):
            logger.info(
                "intervals: assume_all finished [context=%s] after %d round(s); %d tracked int vars, %d tightened",
                ctx_root,
                rounds_run,
                len(self.env),
                len(self.tightened_symbols),
            )

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

            local = IntervalReasoner(modulus=self.p, log_interval_shrinks=self.log_interval_shrinks)
            local.env = dict(seed)
            local.assume_all(
                [body],
                max_iters=max_iters,
                context=f"inject_q quantifier {_fmt_formula(n, max_len=80)}",
            )

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
            base_args = [self._inject_quantifier_bounds(a, inherited, max_iters) for a in n.args()]
            rewritten_args = list(base_args)

            # Local conjunction reasoning: if the conjunction itself forces
            # singleton integer symbols, make these facts explicit.
            # This is sound regardless of polarity because we only add facts
            # implied by the conjunction itself (no inherited seeding here).
            local = IntervalReasoner(modulus=self.p, log_interval_shrinks=self.log_interval_shrinks)
            local.assume_all(
                rewritten_args,
                max_iters=max_iters,
                context=f"inject_q And {_fmt_formula(n, max_len=120)}",
            )
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
                substituted_base = [a.substitute(substitutions).simplify() for a in base_args]
                derived_eqs = rewritten_args[len(base_args):]
                rewritten_args = substituted_base + derived_eqs

            return And(*rewritten_args).simplify()
        if n.is_or():
            # Make negated-disjunction structure explicit so conjunction-local
            # reasoning can infer facts from all inner constraints together.
            if all(a.is_not() for a in n.args()):
                inner = And(*[a.arg(0) for a in n.args()])
                rewritten_inner = self._inject_quantifier_bounds(inner, inherited, max_iters)
                return Not(rewritten_inner).simplify()
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
                if mv is not None and self._eval_int(a, self.env).within_0_p(mv):
                    memo[n] = a
                    return memo[n]
                memo[n] = Mod(go(a), go(m))
                return memo[n]

            if n.is_equals():
                a, b = n.args()
                if (x := _is_mod_p(a, self.p)) is not None and _is_int_const(b) == 0:
                    x_dom = self._eval_int(x, self.env)
                    if x_dom.within_open_pm_p(self.p):
                        memo[n] = Equals(x, Int(0))
                        return memo[n]
                    if (uniq := _unique_multiple_in_domain(x_dom, self.p)) is not None:
                        memo[n] = Equals(x, Int(uniq))
                        return memo[n]
                if (x := _is_mod_p(b, self.p)) is not None and _is_int_const(a) == 0:
                    x_dom = self._eval_int(x, self.env)
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
