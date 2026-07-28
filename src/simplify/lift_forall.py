"""Hoist quantifier bodies: extract ``Not(And(…))`` disjuncts to top-level assertions.

With ``--lift-substitute`` (default on), a pinned quantified variable ``q = expr``
is *substituted* (``q := expr`` in the body, ``q`` dropped) instead of hoisted as
a free variable plus a ``q = expr`` assert. Semantically identical
(``forall q. (q != expr or rest)`` is ``rest[q := expr]``), but it inlines the
pin so downstream congruence/EQ reasoning sees the substituted form directly
rather than having to chain through the pin -- this collapses the before-side
onto the after-side for the inlining soundness VCs (whose pins are the
eliminated-column reconstructions), letting them discharge.
"""
from ..smt.utils import *
from ..utils.args import ARGS
from ..utils.stats import stats_dump


def _qvar_deps(expr: FNode, qvars: frozenset[FNode]) -> frozenset[FNode]:
    """Quantified symbols mentioned by ``expr``."""
    return expr.get_free_variables() & qvars


def _is_potential_lift_pair(d: FNode) -> bool:
    """True if ``d`` is ``Not`` of ``Equals`` or ``Iff`` (candidate for hoisting)."""
    return d.is_not() and (d.arg(0).is_equals() or d.arg(0).is_iff())


def _match_hoistable_eq(eq: FNode, qvars: frozenset[FNode]) -> tuple[FNode, FNode] | None:
    """Match ``Equals`` / ``Iff`` as ``q = expr`` hoistable out of ``qvars``."""
    if eq.is_iff():
        assert eq.arg(0).get_type().is_bool_type() and eq.arg(1).get_type().is_bool_type()
    elif not eq.is_equals():
        return None
    left, right = eq.arg(0), eq.arg(1)
    for vside, expr in ((left, right), (right, left)):
        if not vside.is_symbol():
            continue
        if vside not in qvars:
            continue
        if _qvar_deps(expr, qvars):
            continue
        return vside, eq
    return None


def _match_lift_pair(d: FNode, qvars: frozenset[FNode]) -> tuple[FNode, FNode] | None:
    assert _is_potential_lift_pair(d)
    return _match_hoistable_eq(d.arg(0), qvars)


def _resolve_chain(m: dict[FNode, FNode]) -> dict[FNode, FNode]:
    """Expand a substitution map so no value still references a key (lift order
    can pin ``q2 = f(q1)`` after ``q1`` left the prefix)."""
    resolved = dict(m)
    changed = True
    while changed:
        changed = False
        for q in list(resolved):
            new = resolved[q].substitute(resolved)
            if new != resolved[q]:
                resolved[q] = new
                changed = True
    return resolved


class LiftForallWalker(IdentityDagWalker):
    """Peel pinned equalities out of ``forall`` bodies into ``self.lifted``.

    In substitute mode, inline them into the body (``self.subst_map`` records
    the resolved ``q -> expr`` map for declaration bookkeeping)."""

    def __init__(self, *args, substitute: bool = False, **kwargs):
        """``lifted`` maps each qvar to the full equality node asserted at top level later."""
        super().__init__(*args, **kwargs)
        self.lifted = {}
        self._substitute = substitute
        self.subst_map: dict[FNode, FNode] = {}

    def walk_exists(self, formula, args, **kwargs):
        return formula

    def walk_forall(self, formula, args, **kwargs):
        """Iteratively extract hoistable ``Not(eq)`` disjuncts and shrink the quantifier prefix."""
        # do not recurs, use original body instead
        body = formula.arg(0)
        if not body.is_or():
            return formula

        candidates = set(d for d in body.args() if _is_potential_lift_pair(d))
        qvars = frozenset(formula.quantifier_vars())
        lifted_disjuncts: set[FNode] = set()
        local_map: dict[FNode, FNode] = {}

        progressed = True
        while progressed:
            progressed = False
            for d in sorted(candidates, key=str):
                m = _match_lift_pair(d, qvars)
                if m is not None:
                    lifted, eq = m
                    candidates.remove(d)
                    lifted_disjuncts.add(d)
                    qvars = frozenset(x for x in qvars if x != lifted)
                    if self._substitute:
                        expr = eq.arg(1) if eq.arg(0) == lifted else eq.arg(0)
                        local_map[lifted] = expr
                    else:
                        self.lifted[lifted] = eq
                    progressed = True

        remaining = [a for a in body.args() if a not in lifted_disjuncts]
        if not remaining:
            remaining = [FALSE()]
        qvars_remaining = [v for v in formula.quantifier_vars() if v in qvars]
        body_out = Or(*remaining)
        if self._substitute and local_map:
            resolved = _resolve_chain(local_map)
            body_out = body_out.substitute(resolved)
            self.subst_map.update(resolved)
        if not qvars_remaining:
            return body_out
        return ForAll(qvars_remaining, body_out)


def simplify_lift_forall(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Hoist ``self.lifted`` pins as top-level asserts and insert missing ``declare-fun``s.

    Substitute mode (``--lift-substitute``, default on): inline the pins instead;
    emit no pin asserts and drop the eliminated qvars' declarations."""
    substitute = ARGS().lift_substitute
    w = LiftForallWalker(env=get_env(), substitute=substitute)
    prefix = []
    suffix = []
    in_prefix = True
    declared: set[FNode] = set()
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            declared.add(cmd.args[0])
        if cmd.name == "assert":
            in_prefix = False
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
            suffix.append(cmd)
        elif in_prefix:
            prefix.append(cmd)
        else:
            suffix.append(cmd)

    declared_names = {sym.symbol_name() for sym in declared}

    if substitute:
        # Inlined: no pin asserts, no qvar declarations. Only declare free vars
        # that the inlined exprs introduce and that are not already declared.
        eliminated = set(w.subst_map.keys())
        extra_decls: list[FNode] = []
        for expr in w.subst_map.values():
            for sym in sorted(expr.get_free_variables(), key=lambda s: str(s)):
                if not sym.is_symbol() or sym in eliminated:
                    continue
                if sym.symbol_name() in declared_names:
                    continue
                extra_decls.append(sym)
                declared_names.add(sym.symbol_name())
        declares = [
            script.SmtLibCommand(name="declare-fun", args=[sym, sym.get_type()])
            for sym in extra_decls
        ]
        smt_script.commands = prefix + declares + suffix
        stats_dump(
            "lift_forall",
            {"mode": "substitute", "pins_substituted": len(w.subst_map),
             "new_declarations": len(declares), "hoisted_pin_asserts": 0},
        )
        return smt_script

    extra_decls: list[FNode] = []
    for eq in w.lifted.values():
        for sym in sorted(eq.get_free_variables(), key=lambda s: str(s)):
            if not sym.is_symbol():
                continue
            name = sym.symbol_name()
            if name in declared_names:
                continue
            extra_decls.append(sym)
            declared_names.add(name)

    to_declare: dict[str, FNode] = {sym.symbol_name(): sym for sym in w.lifted.keys()}
    for sym in extra_decls:
        to_declare.setdefault(sym.symbol_name(), sym)
    declares = [
        script.SmtLibCommand(name="declare-fun", args=[sym, sym.get_type()])
        for sym in to_declare.values()
        if sym not in declared
    ] + [
        script.SmtLibCommand(name="assert", args=[eq]) for eq in w.lifted.values()
    ]
    smt_script.commands = prefix + declares + suffix

    n_decl = sum(1 for c in declares if c.name == "declare-fun")
    n_pin = sum(1 for c in declares if c.name == "assert")
    stats_dump(
        "lift_forall",
        {
            "pins_lifted": len(w.lifted),
            "new_declarations": n_decl,
            "hoisted_pin_asserts": n_pin,
        },
    )

    return smt_script
