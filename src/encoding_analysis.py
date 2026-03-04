import json

from .rewriter import rewrite
from .smt.conversion import SmtConverter
from .smt.utils import *
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump


def analyze_aliases():
    """Analyze the aliases in the input."""

    ARGS().memory_encoding = "busat"

    input = load_apc_dump(ARGS().input, 'input')

    with SmtConverter("input", BasicBlock(input["block"])) as conv:
        smt = conv.to_formula_with_axioms(input)
        n = len(conv.bus_interaction_encoder.memory._interactions)
        mem_vars = [
            conv._symbol(f"mem_{i}_{j}", BOOL) for i in range(n) for j in range(i, n)
        ]

    f = And(
        *smt.constraints,
        *smt.axioms,
    )
    f = rewrite(f)

    with Solver(logic=ALL, name=ARGS().solver, solver_options={":timeout": 60000}) as s:
        s.add_assertion(f)

        res = s.solve()
        while res:
            print("Found model, blocking for a different aliasing.")
            nice_model = to_nice_model(s.get_model())
            nice_model = { k: v for k, v in nice_model.items() if k.startswith("mem_") }
            print(json.dumps(nice_model, indent=4))

            blocker = Or(
                v if model[v].is_false() else Not(v)
                for v in mem_vars
            )
            s.add_assertion(blocker)

            res = s.solve()
