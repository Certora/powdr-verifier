from typing import Iterable

from ..smt.utils import *
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


def _intersect_range(
    ranges: dict[FNode, IntInterval], sym: FNode, interval: IntInterval
) -> None:
    """Tighten the currently known interval for ``sym`` with one more bound fact."""
    prev = ranges.get(sym, IntInterval(INF, INF))
    ranges[sym] = prev.intersect(interval)


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

        if formula.is_equals():
            a, b = formula.args()
            ac = _int_constant(a)
            bc = _int_constant(b)
            # Equalities to constants pin the variable to a singleton interval.
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval.const(bc))
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval.const(ac))
            continue

        if formula.is_le():
            a, b = formula.args()
            ac = _int_constant(a)
            bc = _int_constant(b)
            # Non-strict inequalities contribute one-sided bounds as written.
            if b.is_symbol() and ac is not None and ac >= 0:
                _intersect_range(ranges, b, IntInterval(ac, INF))
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(INF, bc))
            continue

        if formula.is_lt():
            a, b = formula.args()
            ac = _int_constant(a)
            bc = _int_constant(b)
            # Strict inequalities are converted to closed integer bounds.
            if b.is_symbol() and ac is not None:
                _intersect_range(ranges, b, IntInterval(ac + 1, INF))
            if a.is_symbol() and bc is not None:
                _intersect_range(ranges, a, IntInterval(INF, bc - 1))

    return ranges, frozenset(protected)


class DeModSubstituter(substituter.Substituter):
    """Eliminate ``mod(x, m)`` when collected top-level facts prove ``0 <= x < m``."""

    def __init__(
        self,
        env=None,
        ranges: dict[FNode, IntInterval] = {},
        protected_constraints: frozenset[FNode] = frozenset(),
    ):
        substituter.Substituter.__init__(self, env=env)
        self.ranges = ranges
        self.protected_constraints = protected_constraints

    @substituter.handles(
        set(operators.ALL_TYPES)
        - frozenset([operators.MOD, operators.FORALL, operators.EXISTS])
    )
    def walk_identity(self, formula, args, **kwargs):
        # Keep witness constraints verbatim so the justification for the learned bounds remains visible.
        if formula in self.protected_constraints:
            return formula
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        qvars = list(formula.quantifier_vars())
        # Outer top-level bounds do not justify rewriting quantified variables.
        inner = DeModSubstituter(
            ranges={sym: interval for sym, interval in self.ranges.items() if sym not in qvars},
            protected_constraints=self.protected_constraints,
        )
        body = inner.substitute(formula.arg(0))
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)

    @substituter.handles(frozenset([operators.MOD]))
    def walk_mod(self, formula, args, **kwargs):
        expr, modulus = args
        # The decision is local to this mod node, but uses the interval accumulated from top-level facts.
        if expr.is_symbol() and (m := _int_constant(modulus)) is not None:
            interval = self.ranges.get(expr)
            if interval is not None and interval.within_0_p(m):
                return keep_comment(expr, formula)
        return keep_comment(Mod(expr, modulus), formula)


def simplify_demod(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run the lightweight de-mod pass over all assertions in an SMT-LIB script."""
    constraints = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    ranges, protected_constraints = extract_symbol_ranges(constraints)
    demod = DeModSubstituter(ranges=ranges, protected_constraints=protected_constraints)
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = demod.substitute(cmd.args[0])
    return smt_script
