from .smt.utils import *
from .utils.args import ARGS
from .utils.profiling import simple_profile

@simple_profile
def check():
    """Check the smt2 file."""

    parser = SmtLibParser()
    logging.info(f"loading from {ARGS().input}")
    smt_script = parser.get_script_fname(str(ARGS().input))

    logging.info(f"checking formula with {ARGS().solver}")
    with Solver(
        logic=AUFNIA, name=ARGS().solver, solver_options={":timeout": 60000}
    ) as s:
        s.set_logic = lambda l: None
        try:
            for cmd in smt_script:
                res = script.evaluate_command(cmd, s)
                if cmd.name == "check-sat":
                    match res:
                        case True:
                            logging.warning("SAT")
                            model = to_nice_model(s.get_model())
                            if ARGS().print_model:
                                print(json.dumps(model, indent=4))
                            if ARGS().dump_model:
                                logging.info(f"dumping model to {ARGS().dump_model}")
                                with open(ARGS().dump_model, "w") as f:
                                    json.dump(model, f, indent=4)
                            return True, model
                        case False:
                            logging.warning("UNSAT")
                            return False, None
                        case _:
                            logging.warning("UNKNOWN")
                            return None, None
        except SolverReturnedUnknownResultError:
            logging.warning("UNKNOWN")
            return None, None
