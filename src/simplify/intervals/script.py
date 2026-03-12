from __future__ import annotations

from ...smt.utils import Bool, FNode, script
from .reasoner import IntervalReasoner


def _has_bottom_domain(reasoner: IntervalReasoner) -> bool:
    return any(dom.is_bottom() for dom in reasoner.env.values())


def _is_simple_atomic_bound(f: FNode) -> bool:
    if not (f.is_le() or f.is_lt() or f.is_equals()):
        return False
    a, b = f.args()
    return (a.is_int_constant() and b.is_symbol()) or (b.is_int_constant() and a.is_symbol())


def simplify_intervals(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run disjunctive interval propagation on all assertions."""
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        return smt_script

    reasoner = IntervalReasoner()
    reasoner.assume_all(assertions)
    inconsistent = _has_bottom_domain(reasoner)

    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        original = cmd.args[0]
        retain = reasoner.must_retain_formula(original)
        if inconsistent:
            cmd.args[0] = Bool(False)
        elif retain:
            # Keep source-level strengthening constraints explicit, but still
            # run quantifier-bound injection and local rewrites.
            cmd.args[0] = reasoner.simplify(
                cmd.args[0],
                prune=False,
                inject_quantifier_bounds=True,
            )
        else:
            cmd.args[0] = reasoner.simplify(
                cmd.args[0],
                prune=True,
                inject_quantifier_bounds=True,
            )
        if (
            not inconsistent
            and not original.is_forall()
            and not original.is_exists()
            and (not retain or not _is_simple_atomic_bound(original))
        ):
            cmd.args[0] = reasoner.inject_root_bounds(cmd.args[0], only_tightened=True)

    return smt_script
