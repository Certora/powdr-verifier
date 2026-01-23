import json

from .utils.basic_block import BasicBlock
from .smt.encoding import build_vc
from .smt.conversion import check_formula, convert_to_smt_formula
from .smt.utils import *

def verify(before: FNode, after: FNode, block: BasicBlock):

    before_smt,_ = convert_to_smt_formula("before", before, block)
    after_smt,_ = convert_to_smt_formula("after", after, block)

    vc = build_vc(before_smt, after_smt)

    match check_formula(vc):
        case False,_:
            print("The two programs are equivalent")
        case None,_:
            print("Could not solve formula, solver returned UNKNOWN")
        case True,model:
            print("The two programs are not equivalent")
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))
