from ..smt.utils import *
from ..rewriter import rewrite
from .intervals import IntervalICPEngine

from .cvc5 import simplify_cvc5
from .z3 import simplify_z3

def simplify_rewrite(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Rewrite each assertion independently with our internal rewriter."""
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = rewrite(cmd.args[0])
    return smt_script


def simplify_intervals(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Run fixed-point integer interval propagation on all assertions."""
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        return smt_script

    engine = IntervalICPEngine()
    engine.assume_all(assertions)

    for cmd in smt_script:
        if cmd.name == "assert":
            if engine.inconsistent:
                cmd.args[0] = Bool(False)
            elif engine.must_retain_formula(cmd.args[0]):
                # Keep source-level bound constraints explicit in the simplified output.
                continue
            else:
                cmd.args[0] = engine.simplify(cmd.args[0], prune=True)

    # Preserve information discovered by propagation even when source constraints
    # simplify away under pruning.
    existing_asserts = {cmd.args[0] for cmd in smt_script if cmd.name == "assert"}
    derived_to_insert: list[FNode] = []
    for derived in engine.derived_range_constraints(only_tightened=True):
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
            out.add_command(script.SmtLibCommand(name="assert", args=[derived]))

    return out
