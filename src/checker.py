"""Run an SMT-LIB script through PySMT with retries, timeouts, and optional model dump.

Parses ``(set-info :status ...)`` as the expected solver outcome, tries a
small grid of random seeds and timeouts, and queries ``:reason-unknown``
when the result is inconclusive.
"""
import json
import logging
import re
import subprocess
from io import StringIO
from pathlib import Path

from .report.action import Action, classify_expected_vs_result
from .smt.utils import *
from .utils.args import ARGS
from .utils.io import SMT_ENCODING, load_smt_script
from .utils.process import communicate_with_timeout
from .utils.stats import init_stats_run, set_stats_tag, stats_enabled, stats_tag_from_path


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


# Budget for the cheap ``check_plain`` pre-try run before the chunked/sliced
# strategies. Splitting the goal ``Or`` into per-disjunct incremental solves
# defeats z3's whole-script QF_NIA/nlsat tactic, which frequently refutes the
# script in a fraction of a second; try that briefly before paying for chunking.
PLAIN_PRETRY_SEC = 5.0

# Check strategies (selected by ``--strategy`` or per-pass below):
#   plain   -- shell out to the z3 binary directly on the input file, whole
#              script, full check budget; no chunking fallback.
#   chunked -- rust checker in per-disjunct chunked mode (python fallback).
#   sliced  -- python COI/CEGAR sliced checker.
CHECK_PLAIN = "plain"
CHECK_CHUNKED = "chunked"
CHECK_SLICED = "sliced"
CHECK_STRATEGY_CHOICES = (CHECK_PLAIN, CHECK_CHUNKED, CHECK_SLICED)
DEFAULT_CHECK_STRATEGY = CHECK_CHUNKED

# Per-pass strategy overrides, mirroring the simplifier's ``STEP_TACTICS``.
# Passes not listed use ``DEFAULT_CHECK_STRATEGY``; an explicit ``--strategy``
# overrides both. ``exec_bus`` VCs solve whole in a few seconds but their
# chunked disjunct solve stalls (benchmark: every successful exec_bus check
# finished plain in <4s and not one was solved by chunking, yet VCs solvable
# whole in 5-14s timed out once chunking took over), so run them plain.
CHECK_STRATEGIES: dict[str, str] = {
    "exec_bus": CHECK_PLAIN,
}


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


def _finalize_result(action: Action, attempt: Action) -> str:
    """Fold ``attempt`` into ``action``: model dump, expected-vs-result logging,
    and the final ``result`` property. Shared by the chunked and sliced paths."""
    action += attempt
    res = attempt.result
    if res == "sat":
        if getattr(ARGS(), "dump_model", None):
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
    return _finalize_result(action, attempt)


def check_smt_script(
    smt_script,
    action: Action,
    *,
    input_for_log: Path | None = None,
    check_timeout: float | None = None,
) -> str:
    """Whole-script pysmt ``Solver`` grid (the python fallback for the ``chunked``
    and ``sliced`` strategies); returns ``sat`` / ``unsat`` / inconclusive."""
    if check_timeout is None:
        check_timeout = getattr(ARGS(), "timeout", None)

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


def _resolve_pretry_z3() -> Path | None:
    """Path to the configured z3 binary, or ``None`` if the pre-try can't run.

    The pre-try shells out to z3 directly on the ``.smt2`` file, so it applies
    only to z3-family solvers (the CLI invocation and stdout parsing below are
    z3-specific). The binary is looked up in the same registry that backs the
    pysmt solver, so it is exactly the z3 the chunked path would use.
    """
    name = ARGS().solver
    if not name.startswith("z3"):
        return None
    try:
        from .smt_backends.pysmt import solvers as _solvers
    except Exception:
        return None
    for s in _solvers:
        if s["name"] == name:
            path = s["path"]
            return path if path.exists() else None
    return None


def _read_status_from_file(path: Path) -> str | None:
    """Extract ``(set-info :status <x>)`` with a line scan (no full parse)."""
    try:
        with open(path, "r", encoding=SMT_ENCODING) as f:
            for line in f:
                if ":status" in line:
                    m = re.search(r":status\s+([A-Za-z-]+)", line)
                    if m:
                        return m.group(1)
    except OSError:
        return None
    return None


def _parse_z3_result(stdout: str | None) -> str | None:
    """Return the ``sat`` / ``unsat`` / ``unknown`` line z3 printed, else None."""
    if not stdout:
        return None
    for line in stdout.splitlines():
        tok = line.strip()
        if tok in ("sat", "unsat", "unknown"):
            return tok
    return None


def _parse_z3_model(stdout: str | None) -> dict[str, Any] | None:
    """Parse z3's ``(get-model)`` output into ``{name: value}`` like ``to_nice_model``.

    z3 prints the model as ``( (define-fun name () Sort value) ... )`` (older
    builds wrap it in ``(model ...)``). Those ``define-fun`` forms are valid
    SMT-LIB, so we strip the outer wrapper and hand them to pysmt's
    ``SmtLibParser`` -- reusing the same constant extraction (:func:`as_constant`,
    array filtering) as :func:`to_nice_model` instead of a bespoke parser.
    Returns ``None`` if the output can't be parsed, so the caller can fall back.
    """
    if not stdout:
        return None
    start = stdout.find("(")
    end = stdout.rfind(")")
    if start < 0 or end <= start:
        return None
    inner = stdout[start + 1 : end].strip()
    if inner.startswith("model"):  # older z3: (model (define-fun ...) ...)
        inner = inner[len("model") :]

    # Import lazily: pulling pysmt's parser at module load initializes its
    # environment before src.smt_backends.pysmt registers the custom MOD
    # operator, which breaks MOD type-checking in the encode path.
    from pysmt.smtlib import commands as smtcmd
    from pysmt.smtlib.parser import SmtLibParser

    try:
        script = SmtLibParser().get_script(StringIO(inner))
    except Exception:
        return None

    model: dict[str, Any] = {}
    for cmd in script:
        if cmd.name != smtcmd.DEFINE_FUN:
            continue
        name, formals, _rtype, body = cmd.args
        if formals:  # only 0-ary symbol assignments
            continue
        if body.is_array_value() or body.is_array_op():
            continue  # arrays are dropped, matching to_nice_model
        model[str(name)] = as_constant(body)
    return model


def check_plain(budget_sec: float = PLAIN_PRETRY_SEC) -> Action | None:
    """Solve the whole script by invoking the z3 binary directly on the ``.smt2``
    file (no pysmt parse, no disjunct chunking).

    This is the ``plain`` strategy (run with the full check budget) and also the
    cheap pre-try run before the ``chunked``/``sliced`` strategies (short
    ``budget_sec``): z3's whole-script QF_NIA/nlsat tactic often refutes the
    script in a fraction of a second, whereas splitting the goal ``Or`` into
    incremental per-disjunct solves can stall for minutes. Takes whatever z3
    decides -- ``sat`` or ``unsat``. When a model dump is requested the ``sat``
    model is read back via ``(get-model)``; if it cannot be parsed, returns
    ``None`` so the caller can fall through to a path that produces the model.
    Returns a finished ``check`` Action if z3 decided, else ``None``.
    """
    z3 = _resolve_pretry_z3()
    if z3 is None:
        return None
    input_path = ARGS().input
    log_key = _display_path(input_path)
    logging.warning("check %s plain (z3, <= %gs)", log_key, budget_sec)

    want_model = bool(getattr(ARGS(), "dump_model", None))
    try:
        smt_text = Path(input_path).read_text(encoding=SMT_ENCODING)
    except OSError:
        return None

    timeout_ms = int(budget_sec * 1000)
    options = {"timeout": timeout_ms, "smt.random_seed": 0, "sat.random_seed": 0}
    cmd = [str(z3), "-smt2", "-in", f"-t:{timeout_ms}", "smt.random_seed=0", "sat.random_seed=0"]
    stdin_text = smt_text if not want_model else (
        "(set-option :produce-models true)\n" + smt_text + "\n(get-model)\n"
    )

    with Action("check") as action:
        action += {"inputs": [input_path]}
        expected = _read_status_from_file(input_path)
        with action.action("solve") as subaction:
            if expected is not None:
                subaction += {"expected": expected}
            model = None
            with subaction.action("check-attempt") as attempt:
                attempt += {"solver": ARGS().solver, "solver_options": options}
                proc = subprocess.Popen(
                    cmd,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
                try:
                    proc.stdin.write(stdin_text)
                    proc.stdin.close()
                except BrokenPipeError:
                    pass
                stdout, _stderr, timed_out = communicate_with_timeout(
                    proc, budget_sec + 5.0
                )
                result = None if timed_out else _parse_z3_result(stdout)
                if result == "sat" and want_model:
                    model = _parse_z3_model(stdout)
                if model is not None:
                    attempt += {"model": model}
                attempt += {"result": result or ("timeout" if timed_out else "unknown")}

            # z3 was inconclusive, or produced a sat we can't hand a model for:
            # let the chunked path take over (it dumps the authoritative model).
            if result not in ("sat", "unsat") or (result == "sat" and want_model and model is None):
                logging.warning(
                    "check %s plain solve inconclusive (%s)",
                    log_key,
                    attempt.result,
                )
                return None

            _dump_model_if_requested(model)
            subaction += {"result": result}
            if model is not None:
                subaction += {"model": model}
            if expected is not None:
                o = classify_expected_vs_result(
                    name=subaction.name, expected=expected, result=result
                )
                if o == "wrong":
                    logging.error("expected %s but got %s", expected, result)
                elif o not in ("success", "timeout"):
                    logging.error("expected %s but got %s", expected, result)
    return action


def _dump_model_if_requested(model: dict[str, Any] | None) -> None:
    if model is not None and getattr(ARGS(), "dump_model", None):
        logging.info("dumping model to %s", ARGS().dump_model)
        with open(ARGS().dump_model, "w") as f:
            json.dump(model, f, indent=4)


_PASSNAME_RE = re.compile(r"_\d+_([a-z][a-z_]*)\.(?:soundness|completeness)")


def _passname_from_input(path: Path) -> str | None:
    """Best-effort pass name from a ``...<step>_<pass>.<kind>.smt2`` filename."""
    m = _PASSNAME_RE.search(Path(path).name)
    return m.group(1) if m else None


def _resolve_check_strategy() -> str:
    """Resolve the check strategy: explicit ``--strategy`` wins, else the per-pass
    override (see ``CHECK_STRATEGIES``), else ``DEFAULT_CHECK_STRATEGY``.

    The pass is taken from ``--optimization-step`` when given, else parsed from
    the input filename so a standalone ``check`` picks the same strategy.
    """
    explicit = getattr(ARGS(), "strategy", None)
    if explicit:
        return explicit
    step = getattr(ARGS(), "optimization_step", None) or _passname_from_input(ARGS().input)
    return CHECK_STRATEGIES.get(step, DEFAULT_CHECK_STRATEGY)


def _plain_timeout_action() -> Action:
    """A finished ``check`` Action reporting ``timeout`` (plain z3 gave up)."""
    with Action("check") as action:
        action += {"inputs": [ARGS().input]}
        expected = _read_status_from_file(ARGS().input)
        with action.action("solve") as subaction:
            if expected is not None:
                subaction += {"expected": expected}
            subaction += {"result": "timeout", "status": "timeout"}
    return action


def check():
    """Check the smt2 file using the resolved per-pass :func:`_resolve_check_strategy`."""

    if stats_enabled():
        init_stats_run(wipe=False)
        set_stats_tag(getattr(ARGS(), "stats_tag", None) or stats_tag_from_path(ARGS().input))

    strategy = _resolve_check_strategy()

    # ``plain``: shell out to the z3 binary directly on the input file with the
    # full check budget; no chunking fallback (report timeout if z3 can't
    # decide). Falls back to the chunked path only if the z3 binary is missing.
    if strategy == CHECK_PLAIN:
        if _resolve_pretry_z3() is not None:
            pre = check_plain(ARGS().timeout)
            return pre if pre is not None else _plain_timeout_action()
        logging.warning("plain check requested but no z3 binary; falling back to chunked")
        strategy = CHECK_CHUNKED

    # ``chunked`` / ``sliced``: a cheap whole-script z3 pre-try first (it often
    # refutes the script in milliseconds), then the richer checker.
    if getattr(ARGS(), "pretry_plain", True):
        pre = check_plain()
        if pre is not None:
            return pre

    # ``chunked`` prefers the rust checker (python chunked is the fallback).
    # ``sliced`` is python-only and never delegates to the rust binary.
    if strategy == CHECK_CHUNKED:
        try:
            from .check.rust import action_from_dict, resolve_checker_bin, run_checker_subprocess

            if resolve_checker_bin() is not None:
                data = run_checker_subprocess(
                    ARGS().input, check_timeout=ARGS().timeout, solve_chunked=True
                )
                return action_from_dict(data)
        except (FileNotFoundError, RuntimeError, json.JSONDecodeError) as e:
            logging.debug("rust checker fallback: %s", e)

    return _check_python(strategy)


def _check_python(strategy: str) -> Action:
    """Python fallback checker: parse the script and solve per ``strategy``
    (``sliced`` COI/CEGAR, or ``chunked`` per-disjunct with a whole-script
    fallback when the goal has no splittable ``Or``)."""
    with Action("check") as action:
        action += {"inputs": [ARGS().input]}

        with action.action("parse"):
            logging.info(f"loading from {ARGS().input}")
            smt_script = load_smt_script(ARGS().input)

        for cmd in smt_script:
            if cmd.name == "set-info" and cmd.args[0] == ":status":
                action += {"expected": cmd.args[1]}
                break

        with action.action("solve") as subaction:
            if action.expected is not None:
                subaction += {"expected": action.expected}

            if strategy == CHECK_SLICED:
                from .check.sliced import check_smt_script_sliced, flatten_script_conjuncts

                ctx, goal = flatten_script_conjuncts(smt_script)
                if goal is None:
                    logging.warning(
                        "no splittable Or-disjunction found, checking entire script"
                    )
                    check_smt_script(smt_script, subaction, input_for_log=ARGS().input)
                else:
                    check_smt_script_sliced(
                        goal,
                        ctx,
                        subaction,
                        input_for_log=ARGS().input,
                        collect_unknowns=getattr(ARGS(), "collect_unknowns", None),
                        debug=getattr(ARGS(), "sliced_debug", False),
                        dump_dir=getattr(ARGS(), "dump_slices", None),
                        dump_all=getattr(ARGS(), "dump_slices_all", False),
                    )
            else:
                goal = _find_largest_or_goal(smt_script)
                if goal is None:
                    logging.warning(
                        "no splittable Or-disjunction found, checking entire script"
                    )
                    check_smt_script(smt_script, subaction, input_for_log=ARGS().input)
                else:
                    check_smt_script_disjuncts(
                        smt_script, goal, subaction, input_for_log=ARGS().input
                    )
        return action
