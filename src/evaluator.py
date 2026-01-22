import json

from .utils.smt_conversion import FormulaWithAxioms, SmtConverter
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

def evaluate(input: dict, smt: FormulaWithAxioms, model: dict[str, int], conv: SmtConverter):

    substitutions = {
        Symbol(name, INT): Int(value) for name, value in model.items()
    }
    interpretations = {
        sym: GenericInterpreter(sym, f)
        for sym, f in conv.bus_interaction_encoder.get_interpreters().items()
    }

    def subs(f: FNode) -> FNode:
        last = None
        cnt = 3
        while last != f and cnt > 0:
            last = f
            f = f.substitute(substitutions, interpretations).simplify()
            cnt -= 1
        return f

    def eval_list(fs: list[FNode]) -> list[FNode]:
        res = True
        for f in fs:
            s = subs(f)
            if not s.is_true():
                print(f"  {f}")
                print(f"  -> {s}")
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
