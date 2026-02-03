import json
import logging

from .utils.basic_block import BasicBlock
from .smt.conversion import SmtConverter
from .smt.utils import *

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

    model = { f'input-{m}': v for m, v in model.items() }

    with SmtConverter("input", BasicBlock(input["block"])) as conv:
        smt = conv.to_formula_with_axioms(input)

        def eval_list(fs: list[FNode]) -> list[FNode]:
            res = True
            for f in fs:
                s = partial_evaluate(f, model, conv.bus_interaction_encoder)
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
        if eval_list(smt.derived):
            print("derived are satisfied")
