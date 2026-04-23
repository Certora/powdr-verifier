from .report.action import Action
from .smt.utils import *
from .utils.args import ARGS
from .utils.profiling import simple_profile

def _get_reason_unknown(solver):
    if not hasattr(solver, "solver_stdin") or not hasattr(solver, "solver_stdout"):
        return None
    try:
        solver.solver_stdin.write("(get-info :reason-unknown)\n")
        solver.solver_stdin.flush()
        return solver.solver_stdout.readline().strip() or None
    except Exception:
        return None

@simple_profile
def check():
    """Check the smt2 file."""

    parser = SmtLibParser()
    logging.info(f"loading from {ARGS().input}")
    smt_script = parser.get_script_fname(str(ARGS().input))

    logging.warning(f"checking {ARGS().input.relative_to(Path.cwd())} with {ARGS().solver}")
    try:
        with (
            Action("check") as action,
            Solver(logic=AUFNIA, name=ARGS().solver, solver_options={":timeout": 60000}) as s
        ):
            action += { "inputs": [ARGS().input] }
            s.set_logic = lambda l: None
            #s.options.debug_interaction = True
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
                if reason := _get_reason_unknown(s):
                    action += { "reason_unknown": reason }
                    logging.warning(f"reason-unknown: {reason}")
            if action.result != action.expected:
                logging.error(f"expected {action.expected} but got {action.result}")
            return action
    except BrokenPipeError:
        return action
