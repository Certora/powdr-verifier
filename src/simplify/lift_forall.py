from typing import Iterable

from ..smt.utils import *


def _is_potential_lift_pair(d: FNode) -> bool:
    return d.is_not() and (d.arg(0).is_equals() or d.arg(0).is_iff())

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
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.lifted = {}

    def walk_forall(self, formula, args, **kwargs):
        # only consider forall over a disjunction
        if not args[0].is_or():
            return formula
        
        # collect potential lift pairs
        candidates = set(d for d in args[0].args() if _is_potential_lift_pair(d))
        # current set of quantified variables
        qvars = frozenset(formula.quantifier_vars())

        progressed = True
        while progressed:
            # loop until no candidate can be lifted
            progressed = False
            for d in list(candidates):
                m = _match_lift_pair(d, qvars)
                if m is not None:
                    lifted, _eq = m
                    candidates.remove(d)
                    self.lifted[lifted] = _eq
                    qvars = frozenset(x for x in qvars if x != lifted)
                    progressed = True

        # remove lifted equalities from the body
        return ForAll(
            [v for v in formula.quantifier_vars() if v in qvars],
            Or(*[a for a in args[0].args() if Not(a) not in self.lifted.values()])
        )


def simplify_lift_forall(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    w = LiftForallWalker(env=get_env())
    prefix = []
    suffix = []
    in_prefix = True
    for cmd in smt_script:
        if cmd.name == "assert":
            in_prefix = False
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
            suffix.append(cmd)
        elif in_prefix:
            prefix.append(cmd)
        else:
            suffix.append(cmd)
    
    declares = [
        script.SmtLibCommand(name="declare-fun", args=[v, v.get_type()]) for v in w.lifted
    ] + [
        script.SmtLibCommand(name="assert", args=[eq]) for eq in w.lifted.values()
    ]
    smt_script.commands = prefix + declares + suffix
    
    return smt_script
