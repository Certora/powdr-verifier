from .report.action import Action
from .smt.utils import *
from .utils.args import ARGS
from .utils.profiling import simple_profile

@simple_profile
def check():
    """Check the smt2 file."""

    parser = SmtLibParser()
    logging.warning(f"loading from {ARGS().input}")
    smt_script = parser.get_script_fname(str(ARGS().input))

    logging.info(f"checking formula with {ARGS().solver}")
    with (
        Action("check") as action,
        Solver(logic=AUFNIA, name=ARGS().solver, solver_options={":timeout": 60000}) as s
    ):
        s.set_logic = lambda l: None
        try:
            for cmd in smt_script:
                if cmd.name == "set-info" and cmd.args[0] == ':status':
                    action += { "expected": cmd.args[1] }
                    continue
                evald = script.evaluate_command(cmd, s)
                if cmd.name == "check-sat":
                    match evald:
                        case True:
                            model = to_nice_model(s.get_model())
                            if ARGS().dump_model:
                                logging.info(f"dumping model to {ARGS().dump_model}")
                                with open(ARGS().dump_model, "w") as f:
                                    json.dump(model, f, indent=4)
                            action += {
                                "result": "sat",
                                "model": model,
                            }
                        case False:
                            action += { "result": "unsat" }
                        case _:
                            action += { "result": "unknown" }
                    break
        except SolverReturnedUnknownResultError:
            action += { "result": "error-unknown" }
        return action
