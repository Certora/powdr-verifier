import json
import logging

from .utils.basic_block import BasicBlock
from .smt.conversion import SmtConverter
from .smt.utils import *

def evaluate(input: dict, model: dict[str, int]):
    """Check which parts of the SMT encoding hold under a provided variable assignment."""

    model = { f'input-{m}': v for m, v in model.items() }

    with SmtConverter("input", BasicBlock(input["block"])) as conv:
        smt = conv.to_formula_with_axioms(input)
        interpreters = conv.bus_interaction_encoder.get_interpreters()

        def eval_list(fs: list[FNode]) -> list[FNode]:
            """Evaluate a list of formulas, printing any that do not simplify to True."""
            res = True
            for f in fs:
                s = partial_evaluate(f, model, interpreters)
                if not s.is_true():
                    print(f"\t{f}")
                    print(f"->\t{s}")
                    res = False
            return res

        logging.debug(f"evaluate on\n{json.dumps(model, indent=4)}")
        if eval_list(smt.constraints):
            print("constraints are satisfied")
        if eval_list(smt.bus_interactions):
            print("bus interactions are satisfied")
        if eval_list(smt.axioms):
            print("axioms are satisfied")
        if eval_list([Equals(v, expr) for v, expr in smt.derived]):
            print("derived are satisfied")
