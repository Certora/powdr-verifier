import json

from .smt import FormulaWithAxioms, check_formula
from .smt_utils import *
from .utils import ARGS

def trace(smt: FormulaWithAxioms):

    f = And(
        *smt.constraints,
        *smt.bus_interactions,
        *smt.axioms,
    )
    if ARGS().use_derived and len(smt.derived) > 0:
        f = And(f, *smt.derived)

    model = to_nice_model(check_formula(f))

    if ARGS().dump_model:
        with open(ARGS().dump_model, 'w') as f:
            json.dump(model, f, indent=4)
    print(json.dumps(model, indent=4))

