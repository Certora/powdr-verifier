"""Evaluate encoded constraints, axioms, and derived columns under a JSON model.

Prints any subformula that does not simplify to ``true`` under
``partial_evaluate`` with bus interpreters from the converter.
"""
import json
import logging

from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json
from .smt.conversion import SmtConverter
from .smt.utils import *


def evaluate():
    """Check which parts of the SMT encoding hold under a provided variable assignment."""

    if ARGS().memory_encoding == "auto":
        # Single-sided like the tracer: the two-sided "auto" alignment decision
        # (resolved in verify's preanalysis) never runs here, and the interface
        # encoding requires an aligned before/after pair. Fall back to the
        # always-sound plain encoding.
        ARGS().memory_encoding = "plain"

    input = load_apc_dump(ARGS().input)
    model = load_json(ARGS().model)

    model = {f"input-{m}": v for m, v in model.items()}

    res = {}

    with SmtConverter("input", BasicBlock(input["block"]), source_path=ARGS().input) as conv:
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
            res["constraints"] = True
        if eval_list(consequence_formulas(smt.consequences)):
            res["consequences"] = True
        if eval_list(smt.axioms):
            res["axioms"] = True
        if eval_list([eq for eqs in smt.derived.values() for eq in eqs]):
            res["derived"] = True

    return res