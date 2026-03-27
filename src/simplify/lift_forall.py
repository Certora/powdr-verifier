from typing import Iterable

from pysmt.walkers import IdentityDagWalker

from ..smt.utils import *


def _or_disjuncts(f: FNode) -> Iterable[FNode]:
    if f.is_or():
        yield from f.args()
    else:
        yield f

def _is_potential_lift_pair(d: FNode) -> bool:
    return d.is_not() and d.arg(0).is_equals()

def _match_lift_pair(d: FNode, qvars: frozenset[FNode]) -> tuple[FNode, FNode] | None:
    assert _is_potential_lift_pair(d)
    eq = d.arg(0)
    left, right = eq.arg(0), eq.arg(1)
    for vside, expr in ((left, right), (right, left)):
        if not vside.is_symbol():
            continue
        if vside not in qvars:
            continue
        if expr.get_free_variables() & qvars:
            continue
        return vside, eq
    return None


class LiftForallWalker(IdentityDagWalker):
    def walk_forall(self, formula, args, **kwargs):
        qvars = frozenset(formula.quantifier_vars())
        skolems = set()
        disjuncts = set()
        discarded = set()
        for d in _or_disjuncts(args[0]):
            if _is_potential_lift_pair(d):
                disjuncts.add(d)
            else:
                discarded.add(d)
        progressed = True
        while progressed:
            progressed = False
            for d in list(disjuncts):
                m = _match_lift_pair(d, qvars)
                if m is not None:
                    lifted, _eq = m
                    disjuncts.remove(d)
                    skolems.add(_eq)
                    qvars = frozenset(x for x in qvars if x != lifted)
                    progressed = True

        if not qvars:
            return args[0]
        return And(
            ForAll([
                v for v in formula.quantifier_vars() if v in qvars
            ], args[0]),
            *skolems
        )


def simplify_lift_forall(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    w = LiftForallWalker(env=get_env())
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
    return smt_script
