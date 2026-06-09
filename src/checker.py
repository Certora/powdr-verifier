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


def _goal_chunk_scripts(smt_script: list, chunks: int) -> list[list] | None:
    """Split the goal disjunction into ``chunks`` scripts, or ``None``.

    The goal of an equivalence check is one large ``Or`` (the negated
    quantified-side constraints). ``base ∧ (D₁ ∨ … ∨ Dₙ)`` is sat iff
    some ``base ∧ (chunk k)`` is sat, so the chunks can be checked
    independently: all-unsat ⟺ unsat, any-sat ⟺ sat (with the model
    carrying over). Each chunk stays far inside the easy regime, where
    the monolithic goal lets the SAT solver interleave case splits
    across unrelated constraint families and occasionally wander.

    Disjuncts are sorted by their (side-prefix-stripped) free-variable
    name sets first, which clusters constraints over the same variable
    families together, so each chunk's case splits stay within related
    constraints.
    """

    def family_key(f):
        def strip(n):
            return n.split("-", 1)[1] if n.startswith(("before-", "after-")) else n

        return tuple(sorted({strip(s.symbol_name()) for s in f.get_free_variables()}))

    goal_idx, goal_args = None, None
    for i, cmd in enumerate(smt_script):
        if cmd.name != "assert" or not cmd.args[0].is_or():
            continue
        if goal_args is None or len(cmd.args[0].args()) > len(goal_args):
            goal_idx, goal_args = i, cmd.args[0].args()
    if goal_idx is None or len(goal_args) < 2 * chunks:
        return None
    disjuncts = sorted(goal_args, key=family_key)
    size = (len(disjuncts) + chunks - 1) // chunks
    out = []
    for k in range(chunks):
        part = disjuncts[k * size : (k + 1) * size]
        if not part:
            continue
        chunk_script = list(smt_script)
        chunk_script[goal_idx] = script.SmtLibCommand(
            name="assert", args=[Or(*part) if len(part) > 1 else part[0]]
        )
        out.append(chunk_script)
    return out


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

        chunk_scripts = (
            _goal_chunk_scripts(smt_script, ARGS().goal_chunks)
            if ARGS().goal_chunks > 1
            else None
        )
        if chunk_scripts is None:
            check_smt_script(smt_script, action, input_for_log=ARGS().input)
            return action

        logging.info(
            "checking goal in %d chunks (%s)", len(chunk_scripts), ARGS().input
        )
        results = []
        for k, chunk_script in enumerate(chunk_scripts):
            with action.action(f"chunk-{k}") as chunk_action:
                res = check_smt_script(
                    chunk_script, chunk_action, input_for_log=ARGS().input
                )
                results.append(res)
            if res == "sat":
                break  # a chunk model is a model of the whole goal
        if "sat" in results:
            overall = "sat"
        elif all(r == "unsat" for r in results):
            overall = "unsat"
        else:
            overall = "unknown"
        if action.expected is not None and overall != action.expected:
            logging.error("expected %s but got %s", action.expected, overall)
        action += {"result": overall, "chunk_results": results}
        return action
