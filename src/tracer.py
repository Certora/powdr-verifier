import json
import logging

from .rewriter import rewrite
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .smt.conversion import SmtConverter
from .smt.utils import *

def trace(input: dict):

    with SmtConverter("input", BasicBlock(input["block"])) as conv:
        smt = conv.to_formula_with_axioms(input)
        interpreters = conv.bus_interaction_encoder.get_interpreters()

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
            model = to_nice_model(model, strip_prefix='input-')
            print(json.dumps(model, indent=4))

            eval_model = { f'input-{m}': v for m, v in model.items() }
            for v,expr in smt.derived:
                evald = partial_evaluate(Equals(v, expr), eval_model, interpreters)
                if not evald.is_true():
                    logging.warning(f"derived column is not true:\n\t{v} = {expr}\n->\t{evald}")

            if ARGS().dump_model:
                logging.info(f"dumping model to {ARGS().dump_model}")
                with open(ARGS().dump_model, 'w') as f:
                    json.dump(model, f, indent=4)
        case False:
            logging.info("no trace found, encoding is UNSAT")
        case None:
            logging.info("no trace found, solver returned UNKNOWN")



