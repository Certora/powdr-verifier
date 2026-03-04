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

    with SmtConverter(None, BasicBlock(input["block"])) as conv:
        smt = conv.to_formula_with_axioms(input)
        n = len(conv.bus_interaction_encoder.memory._interactions)
        mem_vars = [
            conv._symbol(f"memory_{i}_{j}", BOOL) for i in range(n) for j in range(i, n)
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
            model = s.get_model()
            nice_model = to_nice_model(model)
            logging.debug(json.dumps(nice_model, indent=4))

            trues = [ str(v) for v in mem_vars if model[v].is_true() ]
            logging.warning(f"Found model: {", ".join(sorted(trues))}")

            blocker = Or(
                v if model[v].is_false() else Not(v)
                for v in mem_vars
            )
            logging.info(f"adding blocker: {blocker}")
            s.add_assertion(blocker)

            res = s.solve()
