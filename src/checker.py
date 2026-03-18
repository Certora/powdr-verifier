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
        expected_result = None
        try:
            for cmd in smt_script:
                if cmd.name == "set-info" and cmd.args[0] == ':status':
                    match cmd.args[1]:
                        case "sat":
                            expected_result = True
                        case "unsat":
                            expected_result = False
                        case _:
                            expected_result = None
                    continue
                res = script.evaluate_command(cmd, s)
                if cmd.name == "check-sat":
                    correct = expected_result is not None and res == expected_result
                    match res:
                        case True:
                            if not correct:
                                logging.warning("SAT but expected UNSAT")
                            model = to_nice_model(s.get_model())
                            if ARGS().print_model:
                                logging.warning("model:")
                                print(json.dumps(model, indent=4))
                            if ARGS().dump_model:
                                logging.info(f"dumping model to {ARGS().dump_model}")
                                with open(ARGS().dump_model, "w") as f:
                                    json.dump(model, f, indent=4)
                            return True
                        case False:
                            if not correct:
                                logging.warning("UNSAT but expected SAT")
                            return False
                        case _:
                            logging.warning("UNKNOWN")
                            return None
        except SolverReturnedUnknownResultError:
            logging.warning("UNKNOWN")
            return None
