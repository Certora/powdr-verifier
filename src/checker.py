"""Run an SMT-LIB script through PySMT with retries, timeouts, and optional model dump.

Parses ``(set-info :status ...)`` as the expected solver outcome, tries a
small grid of random seeds and timeouts, and queries ``:reason-unknown``
when the result is inconclusive.
"""
import json
import logging
import re
from pathlib import Path

from .report.action import Action
from .smt.utils import *
from .utils.args import ARGS
from .utils.profiling import simple_profile


def _get_reason_unknown(solver):
    """Return the reason string from ``(get-info :reason-unknown)``, or ``None``."""
    if not hasattr(solver, "solver_stdin") or not hasattr(solver, "solver_stdout"):
        return None
    try:
        solver.solver_stdin.write("(get-info :reason-unknown)\n")
        solver.solver_stdin.flush()
        line = solver.solver_stdout.readline().strip()
        if not line:
            return None
        m = re.fullmatch(r'\(\s*:reason-unknown\s+"([^"]*)"\s*\)', line)
        return m.group(1) if m else line
    except Exception:
        return None


def _solver_configs(*, check_timeout: float | None = None):
    """Solver attempts for ``check-sat``. ``check_timeout`` in seconds; converted to Z3 ``timeout`` (ms)."""
    if check_timeout is not None:
        return [
            {
                "name": ARGS().solver,
                "solver_options": {
                    "timeout": int(check_timeout * 1000),
                    "smt.random_seed": 0,
                    "sat.random_seed": 0,
                },
            },
        ]
    return [
        {
            "name": ARGS().solver,
            "solver_options": {
                "timeout": 5000,
                "smt.random_seed": k,
                "sat.random_seed": k,
                "smt.array.weak": "false" if k % 2 == 0 else "true",
            },
        }
        for k in range(4)
    ] + [
        {
            "name": ARGS().solver,
            "solver_options": {
                "timeout": 40000,
                "smt.random_seed": 4,
                "sat.random_seed": 4,
            },
        }
    ]


def _solver_config_label(config):
    """Human-readable label for logging (solver name plus sorted option key/values)."""
    options = ", ".join(
        f"{name}={value}" for name, value in sorted(config["solver_options"].items())
    )
    return f'{config["name"]} ({options})'


def _display_path(path):
    """Prefer a path relative to ``cwd`` for logs; fall back to absolute if not under cwd."""
    if path is None:
        return "<memory>"
    resolved = path.resolve()
    try:
        return resolved.relative_to(resolved.parent.parent)
    except ValueError:
        return resolved


def _run_solver_config(smt_script, config):
    """Execute ``smt_script`` until ``check-sat``, recording sat/unsat/unknown and optional model."""
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
                    if reason := _get_reason_unknown(s):
                        action += {"result": f"unknown-{reason}"}
                    else:
                        action += {"result": "unknown"}
        except BrokenPipeError:
            action += {"result": "error-broken-pipe"}
        return action


def check_smt_script(
    smt_script,
    action: Action,
    *,
    input_for_log: Path | None = None,
    check_timeout: float | None = None,
) -> str:
    """Run the same solver grid as :func:`check`; return ``sat`` / ``unsat`` / inconclusive."""
    last_attempt = None
    log_key = _display_path(input_for_log)
    log = logging.warning if input_for_log is not None else logging.debug
    for config in _solver_configs(check_timeout=check_timeout):
        label = _solver_config_label(config)
        log("check %s with %s", log_key, label)
        attempt = _run_solver_config(smt_script, config)
        action += attempt
        last_attempt = attempt

        if attempt.result in {"sat", "unsat"}:
            break
        log(
            "check %s with %s returned %s, trying next config",
            log_key,
            label,
            attempt.result,
        )
    if last_attempt is None:
        res = "unknown"
    else:
        res = last_attempt.result
    if res == "sat":
        res = last_attempt.result
        action += {"model": last_attempt.model}
        if ARGS().dump_model:
            logging.info("dumping model to %s", ARGS().dump_model)
            with open(ARGS().dump_model, "w") as f:
                json.dump(last_attempt.model, f, indent=4)
    if action.expected is not None and res != action.expected:
        logging.error("expected %s but got %s", action.expected, res)
    action += {"result": res}
    return res


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

        check_smt_script(smt_script, action, input_for_log=ARGS().input)
        return action
