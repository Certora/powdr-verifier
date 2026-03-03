from .smt.utils import *
from .utils.args import ARGS
from .utils.io import load_apc_dump



def check():
    """Check the smt2 file."""

    parser = SmtLibParser()
    logging.warning(f"loading from {ARGS().input}")
    smt_script = parser.get_script_fname(str(ARGS().input))
    f = smt_script.get_last_formula()

    logging.info(f"checking formula with {ARGS().solver}")
    with Solver(
        logic=AUFNIA, name=ARGS().solver, solver_options={":timeout": 60000}
    ) as s:
        try:
            s.add_assertion(f)
            match s.solve():
                case True:
                    logging.warning("SAT")
                    model = s.get_model()
                    if ARGS().print_model:
                        print(json.dumps(to_nice_model(model), indent=4))
                    if ARGS().dump_model:
                        logging.info(f"dumping model to {ARGS().dump_model}")
                        with open(ARGS().dump_model, "w") as f:
                            json.dump(model, f, indent=4)
                    return True, model
                case False:
                    if unsat_msg is not None:
                        logging.warning(unsat_msg)
                    return False, None
                case _:
                    if unknown_msg is not None:
                        logging.warning(unknown_msg)
                    return None, None
        except SolverReturnedUnknownResultError:
            return None, None
