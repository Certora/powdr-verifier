"""Run an SMT-LIB script through PySMT with retries, timeouts, and optional model dump.

Parses ``(set-info :status ...)`` as the expected solver outcome, tries a
small grid of random seeds and timeouts, and queries ``:reason-unknown``
when the result is inconclusive.
"""
import json
import logging
import re
from pathlib import Path

from .report.action import Action, classify_expected_vs_result
from .smt.utils import *
from .utils.args import ARGS


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
                name=config["name"],
                logic=ALL,
                solver_options=config["solver_options"],
            ) as s:
                # The script's own ``(set-logic …)`` is dropped (pysmt has
                # already sent the solver its init logic above); without an
                # array-capable init logic, array-mode scripts fail with
                # "unknown sort 'Array'". ``ALL`` covers both memory encodings
                # and does not slow the QF (plain) path — z3 auto-detects QF.
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


def _find_largest_or_goal(smt_script: list) -> FNode | None:
    """Return the largest top-level ``Or`` assert body, if splittable."""
    goal = None
    n_disjuncts = 0
    for cmd in smt_script:
        if cmd.name != "assert" or not cmd.args[0].is_or():
            continue
        f = cmd.args[0]
        k = len(f.args())
        if k > n_disjuncts:
            goal, n_disjuncts = f, k
    if goal is None or n_disjuncts < 2:
        return None
    return goal


def check_smt_script_disjuncts(
    smt_script,
    goal,
    action: Action,
    *,
    input_for_log: Path | None = None,
    check_timeout: float | None = None,
) -> str:
    """Like :func:`check_smt_script`, but solve the goal ``Or`` one disjunct at a time."""
    log_key = _display_path(input_for_log)
    log = logging.warning if input_for_log is not None else logging.debug
    first = _solver_configs(check_timeout=check_timeout)[0]
    config = {
        "name": first["name"],
        "solver_options": {**first["solver_options"], "timeout": 60_000},
    }
    label = _solver_config_label(config)
    logging.warning("check %s (disjuncts) with %s", log_key, label)
    disjuncts = goal.args()
    with Action("check-attempt") as attempt:
        attempt += {
            "solver": config["name"],
            "solver_options": config["solver_options"],
        }
        try:
            with Solver(
                name=config["name"],
                logic=ALL,
                incremental=True,
                solver_options=config["solver_options"],
            ) as s:
                s.set_logic = lambda l: None
                for cmd in smt_script:
                    if cmd.name == "set-info" and cmd.args[0] == ":status":
                        continue
                    if cmd.name == "assert" and cmd.args[0] is goal:
                        continue
                    if cmd.name == "check-sat":
                        continue
                    script.evaluate_command(cmd, s)
                for k, disjunct in enumerate(disjuncts):
                    s.push()
                    s.add_assertion(disjunct)
                    try:
                        sat = s.solve()
                    except SolverReturnedUnknownResultError:
                        if reason := _get_reason_unknown(s):
                            attempt += {"result": f"unknown-{reason}"}
                        else:
                            attempt += {"result": "unknown"}
                        attempt += {"disjunct_index": k}
                        s.pop()
                        break
                    if sat:
                        attempt += {
                            "result": "sat",
                            "model": to_nice_model(s.get_model()),
                            "disjunct_index": k,
                        }
                        s.pop()
                        break
                    s.pop()
                    s.add_assertion(Not(disjunct))
                else:
                    attempt += {"result": "unsat"}
        except BrokenPipeError:
            attempt += {"result": "error-broken-pipe"}
    action += attempt
    res = attempt.result
    if res == "sat":
        if ARGS().dump_model:
            logging.info("dumping model to %s", ARGS().dump_model)
            with open(ARGS().dump_model, "w") as f:
                json.dump(attempt.model, f, indent=4)
    if action.expected is not None:
        o = classify_expected_vs_result(
            name=action.name, expected=action.expected, result=res
        )
        if o == "wrong":
            logging.error("expected %s but got %s", action.expected, res)
        elif o == "timeout":
            logging.warning(
                "expected %s; solver timed out (result %s)", action.expected, res
            )
        elif o != "success":
            logging.error("expected %s but got %s", action.expected, res)
    action += {"result": res}
    return res


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
    if action.expected is not None:
        o = classify_expected_vs_result(
            name=action.name, expected=action.expected, result=res
        )
        if o == "wrong":
            logging.error("expected %s but got %s", action.expected, res)
        elif o == "timeout":
            logging.warning(
                "expected %s; solver timed out (result %s)", action.expected, res
            )
        elif o != "success":
            logging.error("expected %s but got %s", action.expected, res)
    action += {"result": res}
    return res


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

        if not ARGS().solve_chunked:
            check_smt_script(smt_script, action, input_for_log=ARGS().input)
            return action

        goal = _find_largest_or_goal(smt_script)
        if goal is None:
            logging.warning("no goal found, checking entire script")
            check_smt_script(smt_script, action, input_for_log=ARGS().input)
            return action

        logging.warning(
            "checking goal disjunct-by-disjunct (%d disjuncts) (%s)",
            len(goal.args()),
            ARGS().input,
        )
        check_smt_script_disjuncts(
            smt_script,
            goal,
            action,
            input_for_log=ARGS().input,
        )
        return action
