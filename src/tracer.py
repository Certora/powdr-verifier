import json
import logging

from .utils.rewriter import rewrite
from .utils.smt_conversion import FormulaWithAxioms
from .utils.smt_utils import *
from .utils.args import ARGS

def trace(smt: FormulaWithAxioms):

    f = And(
        *smt.constraints,
        *smt.bus_interactions,
        *smt.axioms,
    )
    if ARGS().use_derived and len(smt.derived) > 0:
        f = And(f, *smt.derived)
    
    f = rewrite(f)

    model = to_nice_model(check_formula(f))
    print(json.dumps(model, indent=4))

    if ARGS().dump_model:
        logging.info(f"dumping model to {ARGS().dump_model}")
        with open(ARGS().dump_model, 'w') as f:
            json.dump(model, f, indent=4)

