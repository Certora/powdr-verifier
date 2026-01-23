import json
import logging

from .rewriter import rewrite
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.smt_conversion import FormulaWithAxioms, convert_to_smt_formula
from .utils.smt_utils import *

def trace(input: dict):

    smt,_ = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

    f = And(
        *smt.constraints,
        *smt.bus_interactions,
        *smt.axioms,
    )
    if ARGS().use_derived and len(smt.derived) > 0:
        f = And(f, *smt.derived)
    
    f = rewrite(f)

    res, model = check_formula(f)

    match res:
        case True:
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))

            if ARGS().dump_model:
                logging.info(f"dumping model to {ARGS().dump_model}")
                with open(ARGS().dump_model, 'w') as f:
                    json.dump(model, f, indent=4)
        case False:
            logging.info("no trace found, encoding is UNSAT")
        case None:
            logging.info("no trace found, solver returned UNKNOWN")



