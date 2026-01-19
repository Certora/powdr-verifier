from .basic_block import BasicBlock
from .encoding import build_vc
from .smt import check_formula, convert_to_smt_formula
from .smt_utils import *

def verify(before: FNode, after: FNode, block: BasicBlock):

    before_smt = convert_to_smt_formula("before", before, block)
    after_smt = convert_to_smt_formula("after", after, block)

    print("before_smt:")
    print(before_smt)
    print("after_smt:")
    print(after_smt)

    vc = build_vc(before_smt, after_smt)

    match check_formula(vc):
        case False:
            print("The two programs are equivalent")
        case None:
            print("Could not solve formula")
        case x:
            print(x)
            print("The two programs are not equivalent")
