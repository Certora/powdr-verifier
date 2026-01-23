import json

from .utils.basic_block import BasicBlock
from .utils.smt_conversion import convert_to_smt_formula
from .utils.smt_utils import *

class GenericInterpreter(FunctionInterpretation):
    def __init__(self, fsym, f):
        self.fsym = fsym
        if isinstance(f, tuple):
            self.concrete, self.symbolic = f
        elif callable(f):
            self.concrete = f
            self.symbolic = None
        else:
            logging.error(f"can not use {f} as interpreter for {fsym}")

    def interpret(self, env, args: list[FNode]) -> FNode:
        if all(arg.is_constant() for arg in args):
            return self.concrete(*[arg.constant_value() for arg in args])
        if self.symbolic is not None:
            if res := self.symbolic(*args):
                return res
        return Function(self.fsym, args)

def evaluate(input: dict, model: dict[str, int]):

    smt,conv = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

    def eval_list(fs: list[FNode]) -> list[FNode]:
        res = True
        for f in fs:
            s = partial_evaluate(f, model, conv.bus_interaction_encoder)
            if not s.is_true():
                print(f"\t{f}")
                print(f"->\t{s}")
                res = False
        return res

    print(json.dumps(model, indent=4))
    print("constraints:")
    if eval_list(smt.constraints):
        print("constraints are satisfied")
    print("bus interactions:")
    if eval_list(smt.bus_interactions):
        print("bus interactions are satisfied")
    print("axioms:")
    if eval_list(smt.axioms):
        print("axioms are satisfied")
    print("derived:")
    if eval_list(smt.derived):
        print("derived are satisfied")
