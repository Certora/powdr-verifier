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


def _solver_configs():
    return [
        {
            "name": ARGS().solver,
            "solver_options": {
                "timeout": 5000,
                "smt.random_seed": k,
                "sat.random_seed": k,
            },
        }
        for k in range(3)
    ] + [
        {
            "name": ARGS().solver,
            "solver_options": {
                "timeout": 45000,
                "smt.random_seed": 3,
                "sat.random_seed": 3,
            },
        }
    ]


def _solver_config_label(config):
    options = ", ".join(
        f"{name}={value}" for name, value in sorted(config["solver_options"].items())
    )
    return f'{config["name"]} ({options})'


def _display_path(path):
    resolved = path.resolve()
    try:
        return resolved.relative_to(Path.cwd())
    except ValueError:
        return resolved


def _run_solver_config(smt_script, config):
    with Action("check-attempt") as action:
        action += {
            "solver": config["name"],
            "solver_options": config["solver_options"],
        }
        try:
            with Solver(
                logic=AUFNIA,
                name=config["name"],
                solver_options=config["solver_options"],
            ) as s:
                s.set_logic = lambda l: None
                try:
                    for cmd in smt_script:
                        if cmd.name == "set-info" and cmd.args[0] == ":status":
                            continue
                        evald = script.evaluate_command(cmd, s)
                        if cmd.name == "check-sat":
                            match evald:
                                case True:
                                    action += {
                                        "result": "sat",
                                        "model": to_nice_model(s.get_model()),
                                    }
                                case False:
                                    action += {"result": "unsat"}
                                case _:
                                    action += {"result": "unknown"}
                            break
                except SolverReturnedUnknownResultError:
                    action += {"result": "error-unknown"}
                    if reason := _get_reason_unknown(s):
                        action += {"reason_unknown": reason}
                        logging.warning(f"reason-unknown: {reason}")
        except BrokenPipeError:
            action += {"result": "error-broken-pipe"}
        return action


@simple_profile
def check():
    """Check the smt2 file."""

    parser = SmtLibParser()
    logging.info(f"loading from {ARGS().input}")
    smt_script = list(parser.get_script_fname(str(ARGS().input)))

    with Action("check") as action:
        action += {"inputs": [ARGS().input]}
        for cmd in smt_script:
            if cmd.name == "set-info" and cmd.args[0] == ":status":
                action += {"expected": cmd.args[1]}
                break

        last_attempt = None
        for config in _solver_configs():
            label = _solver_config_label(config)
            logging.warning(f"checking {_display_path(ARGS().input)} with {label}")
            attempt = _run_solver_config(smt_script, config)
            action += attempt
            last_attempt = attempt

            if attempt.result in {"sat", "unsat"}:
                action += {"result": attempt.result}
                if attempt.result == "sat":
                    action += {"model": attempt.model}
                    if ARGS().dump_model:
                        logging.info(f"dumping model to {ARGS().dump_model}")
                        with open(ARGS().dump_model, "w") as f:
                            json.dump(attempt.model, f, indent=4)
                break

            logging.warning(f"{label} returned {attempt.result}, trying next config")

        if action.result is None and last_attempt is not None:
            action += {"result": last_attempt.result}
            if last_attempt.reason_unknown is not None:
                action += {"reason_unknown": last_attempt.reason_unknown}

        if action.expected is not None and action.result != action.expected:
            logging.error(f"expected {action.expected} but got {action.result}")
        return action
