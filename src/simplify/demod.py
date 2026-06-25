"""Demodulation / interval-aware simplification of top-level asserted constraints."""
from typing import Iterable

from pysmt.walkers import IdentityDagWalker

from ..smt.utils import *
from ..utils.stats import stats_dump, stats_enabled
from ..utils.args import ARGS
from .intervals.domain import INF, IntInterval


def _int_constant(node: FNode) -> int | None:
    """Return the integer value of a literal node, or ``None`` for non-literals."""
    if node.node_type() == operators.INT_CONSTANT:
        return int(node.constant_value())
    return None


def _flatten_top_level_constraints(formulas: Iterable[FNode]) -> Iterable[FNode]:
    """Flatten only top-level conjunctions so each asserted fact is considered independently."""
    for formula in formulas:
        if formula.is_and():
            yield from _flatten_top_level_constraints(formula.args())
        else:
            yield formula


def _self_mod_symbol(formula: FNode) -> tuple[FNode, int] | None:
    """Recognize equalities of the form ``x = mod(x, m)`` or ``mod(x, m) = x``."""
    if not formula.is_equals():
        return None
    a, b = formula.args()
    # Recognize x = mod(x, m) as an explicit bound witness for 0 <= x < m.
    if a.is_symbol() and b.is_mod():
        expr, mod = b.args()
        if expr == a and (m := _int_constant(mod)) is not None:
            return a, m
    if b.is_symbol() and a.is_mod():
        expr, mod = a.args()
        if expr == b and (m := _int_constant(mod)) is not None:
            return b, m
    return None


def _normalized_relation(formula: FNode) -> tuple[str, FNode, FNode] | None:
    """Return a normalized arithmetic relation, pushing a top-level negation inward."""
    negated = formula.is_not()
    relation = formula.arg(0) if negated else formula

    if relation.is_equals():
        return ("!=", *relation.args()) if negated else ("=", *relation.args())
    if relation.is_lt():
        return (">=", *relation.args()) if negated else ("<", *relation.args())
    if relation.is_le():
        return (">", *relation.args()) if negated else ("<=", *relation.args())
    return None


def _intersect_range(
    ranges: dict[FNode, IntInterval], sym: FNode, interval: IntInterval
) -> None:
    """Tighten the currently known interval for ``sym`` with one more bound fact."""
    prev = ranges.get(sym, IntInterval(INF, INF))
    ranges[sym] = prev.intersect(interval)


def _normalize_arith_under_mod(e: FNode, m: int) -> FNode:
    """Congruence mod ``m``: ``-`` as ``+`` / ``*`` with ``m-1``; int literals as ``k % m``."""
    assert m > 0
    if (ic := _int_constant(e)) is not None:
        return Int(ic % m)
    if e.is_plus():
        return Plus(*[_normalize_arith_under_mod(a, m) for a in e.args()])
    if e.is_minus():
        a, b = e.args()
        na = _normalize_arith_under_mod(a, m)
        nb = _normalize_arith_under_mod(b, m)
        neg1 = Int(m - 1)
        return Plus(na, Times(neg1, nb))
    if e.is_times():
        return Times(*[_normalize_arith_under_mod(a, m) for a in e.args()])
    if e.is_ite():
        c, thn, els = e.args()
        return Ite(
            c,
            _normalize_arith_under_mod(thn, m),
            _normalize_arith_under_mod(els, m),
        )
    return e


def _demod_rewrite_eqmod_zero_equals(lhs: FNode, rhs: FNode) -> FNode | None:
    """Replaces ``Mod(a*x + b, p) = 0`` (field ``p``) with ``x = (-b/a) mod p``."""
    if not lhs.is_mod() or not rhs.is_zero():
        return None
    expr, modulus = lhs.args()
    p = int(ARGS().field_type.value)
    if not modulus.is_int_constant() or int(modulus.constant_value()) != p:
        return None
    lf = linear_form(expr)
    if lf is None:
        return None
    terms, const = lf
    terms = {s: a % p for s, a in terms.items() if a % p != 0}
    if len(terms) != 1:
        return None
    sym, a = next(iter(terms.items()))
    if a == 0 or (a == 1 and const % p == 0):
        return None
    val = (-const * pow(a, -1, p)) % p
    return Equals(sym, wrap_mod(Int(val)))


class _EqModZeroWalker(IdentityDagWalker):
    """Apply ``_demod_rewrite_eqmod_zero_equals`` at every ``Equals`` node."""

    def walk_equals(self, formula, args, **kwargs):
        lhs, rhs = args
        rep = _demod_rewrite_eqmod_zero_equals(lhs, rhs)
        if rep is not None:
            return rep
        return self.mgr.Equals(lhs, rhs)


def extract_symbol_ranges(
    formulas: Iterable[FNode],
) -> tuple[dict[FNode, IntInterval], frozenset[FNode]]:
    """Extract simple top-level symbol ranges and the witness constraints that produced them."""
    ranges: dict[FNode, IntInterval] = {}
    protected: set[FNode] = set()

    # Only top-level constraints contribute facts; nested structure is left untouched.
    for formula in _flatten_top_level_constraints(formulas):
        if (res := _self_mod_symbol(formula)) is not None:
            sym, modulus = res
            # A self-mod equality is treated as a direct witness for the full range.
            _intersect_range(ranges, sym, IntInterval(0, modulus - 1))
            protected.add(formula)
            continue

        if (relation := _normalized_relation(formula)) is None:
            continue

        op, a, b = relation
        if op == "=":
            ac = _int_constant(a)
            bc = _int_constant(b)
            # Equalities to constants pin the variable to a singleton interval.
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval.const(bc))
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval.const(ac))
            continue

        ac = _int_constant(a)
        bc = _int_constant(b)
        if op == "<=":
            # Non-strict inequalities contribute one-sided bounds as written.
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval(ac, INF))
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(INF, bc))
            continue

        if op == "<":
            # Strict inequalities are converted to closed integer bounds.
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval(ac + 1, INF))
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(INF, bc - 1))
            continue

        if op == ">=":
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(bc, INF))
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval(INF, ac))
            continue

        if op == ">":
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(bc + 1, INF))
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval(INF, ac - 1))

    return ranges, frozenset(protected)


class DeModSubstituter(substituter.Substituter):
    """Eliminate ``mod(x, m)`` when collected top-level facts prove ``0 <= x < m``."""

    def __init__(
        self,
        env=None,
        ranges: dict[FNode, IntInterval] = {},
        protected_constraints: frozenset[FNode] = frozenset(),
        stats: dict[str, int] | None = None,
    ):
        """``ranges``: learned bounds per symbol; ``protected_constraints`` stay unmodified."""
        substituter.Substituter.__init__(self, env=env)
        self.ranges = ranges
        self.protected_constraints = protected_constraints
        self._stats = stats

    def _bump(self, key: str) -> None:
        if self._stats is not None:
            self._stats[key] = self._stats.get(key, 0) + 1

    @substituter.handles(
        set(operators.ALL_TYPES)
        - frozenset([operators.MOD, operators.FORALL, operators.EXISTS])
    )
    def walk_identity(self, formula, args, **kwargs):
        """Recurse unchanged except skip rewriting for ``protected_constraints``."""
        # Keep witness constraints verbatim so the justification for the learned bounds remains visible.
        if formula in self.protected_constraints:
            return formula
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        """Do not apply outer learned bounds to quantified variables."""
        qvars = list(formula.quantifier_vars())
        # Outer top-level bounds do not justify rewriting quantified variables.
        inner = DeModSubstituter(
            ranges={sym: interval for sym, interval in self.ranges.items() if sym not in qvars},
            protected_constraints=self.protected_constraints,
            stats=self._stats,
        )
        body = inner.substitute(formula.arg(0))
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)

    @substituter.handles(frozenset([operators.MOD]))
    def walk_mod(self, formula, args, **kwargs):
        """Fold constant mod, push mod through ``ite``, or drop ``mod`` when in-range."""
        expr, modulus = args
        if (mc := _int_constant(modulus)) is not None and mc > 0:
            expr = _normalize_arith_under_mod(expr, mc)
        if (ec := _int_constant(expr)) is not None and (mc := _int_constant(modulus)) is not None and mc != 0:
            self._bump("const_eval")
            return keep_comment(Int(ec % mc), formula)
        if expr.is_ite():
            cond, thn, els = expr.args()
            inner = DeModSubstituter(
                ranges=self.ranges,
                protected_constraints=self.protected_constraints,
                stats=self._stats,
            )
            self._bump("into_ite")
            return keep_comment(
                Ite(
                    cond,
                    inner.substitute(Mod(thn, modulus)),
                    inner.substitute(Mod(els, modulus)),
                ),
                formula,
            )
        # The decision is local to this mod node, but uses the interval accumulated from top-level facts.
        if expr.is_symbol() and (m := _int_constant(modulus)) is not None:
            interval = self.ranges.get(expr)
            if interval is not None and interval.within_0_p(m):
                self._bump("elim_by_range")
                return keep_comment(expr, formula)
        return keep_comment(Mod(expr, modulus), formula)


def simplify_demod(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Run the lightweight de-mod pass over all assertions in an SMT-LIB script."""
    eqmod_walker = _EqModZeroWalker(env=get_env())
    eqmod_asserts_changed = 0
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        old = cmd.args[0]
        new = eqmod_walker.walk(old)
        if new is not old:
            eqmod_asserts_changed += 1
        cmd.args[0] = keep_comment(new, old)

    constraints = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    ranges, protected_constraints = extract_symbol_ranges(constraints)
    stats: dict[str, int] | None = (
        {"eqmod_asserts_changed": eqmod_asserts_changed} if stats_enabled() else None
    )
    demod = DeModSubstituter(
        ranges=ranges,
        protected_constraints=protected_constraints,
        stats=stats,
    )
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = demod.substitute(cmd.args[0])
    stats_dump(
        "demod",
        {
            "range_symbols": len(ranges),
            "protected_range_constraints": len(protected_constraints),
            **(stats or {"eqmod_asserts_changed": eqmod_asserts_changed}),
        },
    )
    return smt_script
