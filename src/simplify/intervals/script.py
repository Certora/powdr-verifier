from __future__ import annotations

from ...smt.utils import Bool, FNode, script
from .reasoner import IntervalReasoner


def _has_bottom_domain(reasoner: IntervalReasoner) -> bool:
    return any(dom.is_bottom() for dom in reasoner.env.values())


def simplify_intervals(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run disjunctive interval propagation on all assertions."""
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        return smt_script

    reasoner = IntervalReasoner()
    reasoner.assume_all(assertions)
    inconsistent = _has_bottom_domain(reasoner)

    free_vars = set()
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        if inconsistent:
            cmd.args[0] = Bool(False)
        elif reasoner.must_retain_formula(cmd.args[0]):
            # Keep source-level strengthening constraints explicit.
            pass
        else:
            cmd.args[0] = reasoner.simplify(
                cmd.args[0],
                prune=True,
                inject_quantifier_bounds=True,
            )
        free_vars.update(cmd.args[0].get_free_variables())

    # Preserve discovered top-level range information even when source constraints simplify away.
    existing_asserts = {cmd.args[0] for cmd in smt_script if cmd.name == "assert"}
    derived_to_insert: list[FNode] = []
    for derived in reasoner.derived_range_constraints(only_tightened=True):
        if derived not in existing_asserts:
            derived_to_insert.append(derived)
            existing_asserts.add(derived)

    if not derived_to_insert:
        return smt_script

    # Keep derived facts in the assertion block, right before satisfiability checks.
    out = script.SmtLibScript()
    inserted = False
    for cmd in smt_script:
        if not inserted and cmd.name in {"check-sat", "check-sat-assuming"}:
            for derived in derived_to_insert:
                out.add_command(script.SmtLibCommand(name="assert", args=[derived]))
            inserted = True
        out.add_command(cmd)

    if not inserted:
        for derived in derived_to_insert:
            if derived.get_free_variables().issubset(free_vars):
                out.add_command(script.SmtLibCommand(name="assert", args=[derived]))

    return out
