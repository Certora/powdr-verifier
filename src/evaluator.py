import json

from .utils.smt_utils import *

from .utils.smt_conversion import FormulaWithAxioms

class ModInterpreter(FunctionInterpretation):
    def __init__(self):
        pass

    def interpret(self, env, args: list[FNode]) -> FNode:
        assert len(args) == 2, "Mod interpreter expects 2 arguments"
        x,y = args
        if x.is_constant() and y.is_constant():
            return Int(x.constant_value() % y.constant_value())
        return Function(UF_MOD, args)

def evaluate(input: dict, smt: FormulaWithAxioms, model: dict[str, int]):

    substitutions = {
        Symbol(name, INT): Int(value) for name, value in model.items()
    }
    interpretations = {
        UF_MOD: ModInterpreter(),
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

    assert len(input["constraints"]) == len(smt.constraints), "The number of constraints is different"
    assert len(input["bus_interactions"]) == len(smt.bus_interactions), "The number of bus interactions is different"
    assert len(input["derived_columns"]) == len(smt.derived), "The number of derived is different"
    
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
