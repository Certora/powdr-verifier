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

    model = check_formula(f)
        
    print(json.dumps(to_nice_model(model), indent=4))

