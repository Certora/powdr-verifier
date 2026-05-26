"""Hoist quantifier bodies: extract ``Not(And(…))`` disjuncts to top-level assertions."""
from ..smt.utils import *


def _qvar_deps(expr: FNode, qvars: frozenset[FNode]) -> frozenset[FNode]:
    """Quantified symbols mentioned by ``expr``."""
    return expr.get_free_variables() & qvars


def _is_potential_lift_pair(d: FNode) -> bool:
    """True if ``d`` is ``Not`` of an equality or boolean ``Iff`` (candidate for hoisting)."""
    return d.is_not() and (d.arg(0).is_equals() or d.arg(0).is_iff())


def _match_hoistable_eq(eq: FNode, qvars: frozenset[FNode]) -> tuple[FNode, FNode] | None:
    """Match ``Equals`` / bool ``Iff`` as ``q = expr`` hoistable out of ``qvars``."""
    if eq.is_iff():
        if not (eq.arg(0).get_type().is_bool_type() and eq.arg(1).get_type().is_bool_type()):
            return None
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


class LiftForallWalker(IdentityDagWalker):
    """Peel pinned equalities out of ``forall`` bodies into ``self.lifted``."""

    def __init__(self, *args, **kwargs):
        """``lifted`` maps each qvar to the full equality node asserted at top level later."""
        super().__init__(*args, **kwargs)
        self.lifted = {}
    
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

        progressed = True
        while progressed:
            progressed = False
            for d in sorted(candidates, key=str):
                m = _match_lift_pair(d, qvars)
                if m is not None:
                    lifted, eq = m
                    candidates.remove(d)
                    self.lifted[lifted] = eq
                    lifted_disjuncts.add(d)
                    qvars = frozenset(x for x in qvars if x != lifted)
                    progressed = True

        remaining = [a for a in body.args() if a not in lifted_disjuncts]
        if not remaining:
            remaining = [FALSE()]
        qvars_remaining = [v for v in formula.quantifier_vars() if v in qvars]
        body_out = Or(*remaining)
        if not qvars_remaining:
            return body_out
        return ForAll(qvars_remaining, body_out)


def simplify_lift_forall(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Hoist ``self.lifted`` pins as top-level asserts and insert missing ``declare-fun``s."""
    w = LiftForallWalker(env=get_env())
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

    return smt_script
