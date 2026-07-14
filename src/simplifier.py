"""SMT-LIB simplification pipeline driven by colon-separated tactic names.

Each tactic mutates or inspects a parsed script in place; optional per-step
dumps are controlled via ``--dump-steps``. Use ``--pretty`` for pretty-printed output.
"""
import copy
import logging
import os
import signal
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, TypeVar

from .report.action import Action
from .smt.utils import *
from .smt_backends.pysmt import write_smtlib_script
from .utils.args import ARGS
from .utils.io import open_file
from .utils.stats import init_stats_run, set_stats_tag, stats_enabled, stats_tag_from_path, clear_pass_action, set_pass_action

from .simplify.witness import simplify_witnesses
from .simplify.domain_probe import simplify_domain_probe
from .simplify import (
    check_isqf,
    simplify_bounds,
    simplify_cvc5,
    simplify_demod,
    simplify_evaluate,
    simplify_flatten_outer_array,
    simplify_bitwise,
    simplify_intervals,
    simplify_intervals2,
    simplify_lift_forall,
    simplify_mod_inv,
    simplify_normalize,
    simplify_model,
    simplify_nnf,
    simplify_rewrite,
    simplify_skolem,
    simplify_solve_eqs,
    simplify_solve_store_eqs,
    simplify_rewrite_store_eqs,
    simplify_ufnorm,
    simplify_z3,
)
from .simplify.rust import run_rust_pipeline, rust_step_action_props

_T = TypeVar("_T")

TACTIC_QEPREFIX = "nnf:skolem:lift:witness:demod:isqf"

DEFAULT_TACTIC = (
    TACTIC_QEPREFIX + ":bounds:demod:normalize:bitwise:rewrite:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:ufnorm:normalize:demod"
)

# Custom colon-separated pipelines keyed by powdr optimization pass name (e.g. ``remove_free``).
STEP_TACTICS: dict[str, str] = {
    "exec_bus": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod",
    "loop_iteration": TACTIC_QEPREFIX + ":bounds:demod:normalize:bitwise:mod_inv:demod:z3-propagate-values:normalize:demod",
    "solver": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod",
    "substitute_bus_interactio_fields": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod",
}


@dataclass(frozen=True)
class TacticParts:
    """Parsed tactic token: optional executor prefix, pass name, dash suffix args."""

    executor: str
    base: str
    suffix: list[str]

    def raw(self) -> str:
        body = self.base if not self.suffix else f"{self.base}-{'-'.join(self.suffix)}"
        if self.executor:
            return f"{self.executor}#{body}"
        return body


def _split_tactic(raw_tactic: str) -> TacticParts:
    """Split ``z3-foo``, ``p#z3-foo``, or ``r#z3-foo`` into executor, base, and suffix."""
    executor = ""
    inner = raw_tactic
    if len(raw_tactic) >= 2 and raw_tactic[1] == "#":
        executor = raw_tactic[0]
        inner = raw_tactic[2:]
    base, *dash_suffix = inner.split("-", 1)
    return TacticParts(executor=executor, base=base, suffix=dash_suffix)


def resolve_tactic(tactic: str, optimization_step: str | None = None) -> str:
    """Resolve ``default`` and per-step overrides to a colon-separated pipeline."""
    if tactic != "default":
        return tactic
    if optimization_step and optimization_step in STEP_TACTICS:
        return STEP_TACTICS[optimization_step]
    return DEFAULT_TACTIC


def _pipeline_groups(
    tactic: str, optimization_step: str | None = None
) -> list[tuple[str, list[str]]]:
    resolved = resolve_tactic(tactic, optimization_step)
    default_executor = getattr(ARGS(), "default_executor", "p")
    return _group_tactics(resolved.split(":"), default_executor=default_executor)


def _load_script(path: Path) -> script.SmtLibScript:
    with open_file(path, "r") as f:
        parser = SmtLibParser()
        logging.info(f"loading from {f.name}")
        return parser.get_script(f)


class _PassTimeout(Exception):
    pass


def _run_with_itimer(seconds: float, fn: Callable[[], _T]) -> tuple[bool, _T | None]:
    """Run ``fn`` under a real-time itimer. Returns ``(timed_out, value)``."""

    def _on_alarm(_signum, _frame):
        raise _PassTimeout()

    prev = signal.signal(signal.SIGALRM, _on_alarm)
    try:
        signal.setitimer(signal.ITIMER_REAL, float(seconds))
        return False, fn()
    except _PassTimeout:
        return True, None
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0.0)
        signal.signal(signal.SIGALRM, prev)


def _group_tactics(
    tactics: list[str],
    *,
    default_executor: str = "p",
) -> list[tuple[str, list[str]]]:
    groups: list[tuple[str, list[str]]] = []
    for raw in tactics:
        match _split_tactic(raw).executor:
            case "p":
                executor = "p"
            case "r":
                executor = "r"
            case "":
                executor = default_executor
            case bad:
                logging.error("ignoring tactic with unknown executor %r: %s", bad, raw)
                continue
        if groups and groups[-1][0] == executor:
            groups[-1][1].append(raw)
        else:
            groups.append((executor, [raw]))
    return groups


def _backup_script(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    backup = script.SmtLibScript()
    if smt_script.annotations is not None:
        backup.annotations = copy.copy(smt_script.annotations)
    backup.commands = [cmd._replace(args=list(cmd.args)) for cmd in smt_script.commands]
    return backup


def _attach_rust_step_actions(
    parent: Action,
    raw_tactics: list[str],
    steps: list[dict],
    *,
    batch_end_ns: int,
) -> None:
    if len(steps) != len(raw_tactics):
        logging.warning(
            "rust step stats count %d != tactic count %d",
            len(steps),
            len(raw_tactics),
        )
        steps = [
            steps[i] if i < len(steps) else {"running_time": 0.0}
            for i in range(len(raw_tactics))
        ]
    total_ns = sum(int(float(step.get("running_time", 0.0)) * 1e9) for step in steps)
    cursor_ns = batch_end_ns - total_ns
    for raw, step in zip(raw_tactics, steps):
        rt = float(step.get("running_time", 0.0))
        rt_ns = int(rt * 1e9)
        enter_ns = cursor_ns
        exit_ns = cursor_ns + rt_ns
        cursor_ns = exit_ns
        child = Action(
            raw,
            enter_time=enter_ns,
            exit_time=exit_ns,
            running_time=rt,
            executor="rust",
        )
        props = rust_step_action_props(step)
        if props:
            child += props
        parent += child


def _run_python_passes(
    parent: Action,
    smt_script: script.SmtLibScript,
    raw_tactics: list[str],
    *,
    deadline: float | None = None,
    output: Path | None = None,
    step_index: int = 0,
    dump_steps: bool = False,
    rust_fallback_batch: str | None = None,
) -> tuple[script.SmtLibScript, int]:
    if rust_fallback_batch is not None:
        with parent.action("rust-fallback") as fb:
            fb += {"fallback": True, "reason": "error", "batch": rust_fallback_batch}

    cur = smt_script
    idx = step_index
    for raw_tactic in raw_tactics:
        idx += 1
        parts = _split_tactic(raw_tactic)
        remaining = (
            deadline - time.monotonic() - 2 if deadline is not None else float("inf")
        )

        logging.info("simplifying with %s", raw_tactic)
        with parent.action(raw_tactic) as subaction:
            prev_action = set_pass_action(subaction)
            try:
                subaction += {"executor": "python"}
                if deadline is not None and remaining <= 0:
                    logging.info(
                        "skipping simplifier pass %s (no time budget)", raw_tactic
                    )
                    subaction += {"result": "skipped", "reason": "no-budget"}
                    continue

                backup_script = _backup_script(cur)
                backup_pretty = ARGS().pretty

                def run_step():
                    return _apply_tactic_pass(
                        TacticParts(
                            executor="", base=parts.base, suffix=parts.suffix
                        ),
                        cur,
                        subaction,
                    )

                if deadline is not None:
                    timed_out, step_script = _run_with_itimer(remaining, run_step)
                else:
                    timed_out = False
                    step_script = run_step()

                if timed_out:
                    cur = backup_script
                    ARGS().pretty = backup_pretty
                    logging.warning(
                        "simplifier pass %s hit timeout, skipping", raw_tactic
                    )
                    subaction += {"result": "timeout"}
                else:
                    assert step_script is not None
                    cur = step_script
                    _ensure_declarations_for_asserts(cur)
            finally:
                clear_pass_action(prev_action)

        if dump_steps and output is not None:
            stem = (
                output.name[: -len(output.suffix)] if output.suffix else output.name
            )
            dump_file = output.with_name(f"{stem}.{idx:02d}.{raw_tactic}.smt2")
            with open_file(dump_file, "w") as out:
                logging.info("dumping intermediate formula to %s", out.name)
                write_smtlib_script(cur, out)

    return cur, idx


def _run_rust_tactics(
    parent: Action,
    smt_script: script.SmtLibScript | None,
    raw_tactics: list[str],
    *,
    timeout: float | None = None,
    profile_input: Path | None = None,
    profile_output: Path | None = None,
    input_path: Path | None = None,
    rust_output_path: Path | None = None,
    dump_steps_output: Path | None = None,
    dump_step_offset: int = 0,
    parse_output: bool = True,
) -> script.SmtLibScript | None:
    pipeline = ":".join(raw_tactics)
    try:
        smt_script, steps = run_rust_pipeline(
            smt_script,
            pipeline,
            timeout=timeout,
            profile_input=profile_input,
            profile_output=profile_output,
            input_path=input_path,
            output_path=rust_output_path,
            dump_steps_output=dump_steps_output,
            dump_step_offset=dump_step_offset,
            parse_output=parse_output,
        )
    except (FileNotFoundError, RuntimeError) as exc:
        logging.warning(
            "rust simplifier batch %s failed (%s), falling back to python",
            pipeline,
            exc,
        )
        if smt_script is None:
            assert input_path is not None
            smt_script = _load_script(input_path)
        deadline = (
            time.monotonic() + float(timeout) if timeout is not None else None
        )
        smt_script, _ = _run_python_passes(
            parent,
            smt_script,
            raw_tactics,
            deadline=deadline,
            output=dump_steps_output,
            step_index=dump_step_offset,
            dump_steps=getattr(ARGS(), "dump_steps", False),
            rust_fallback_batch=pipeline,
        )
        return smt_script

    _attach_rust_step_actions(
        parent, raw_tactics, steps, batch_end_ns=time.perf_counter_ns()
    )
    return smt_script


def _apply_tactic_pass(
    parts: TacticParts,
    smt_script: script.SmtLibScript,
    subaction,
) -> script.SmtLibScript:
    base = parts.base
    dash_suffix = parts.suffix
    match base:
        case "witness":
            return simplify_witnesses(smt_script, subaction)
        case "flatten_outer_array":
            return simplify_flatten_outer_array(smt_script, subaction)
        case "solve_eqs":
            return simplify_solve_eqs(smt_script, subaction)
        case "solve_store_eqs":
            return simplify_solve_store_eqs(smt_script, subaction)
        case "rewrite_store_eqs":
            return simplify_rewrite_store_eqs(smt_script, subaction)
        case "bounds":
            return simplify_bounds(smt_script, subaction)
        case "nnf":
            return simplify_nnf(smt_script, subaction)
        case "lift":
            return simplify_lift_forall(smt_script, subaction)
        case "rewrite":
            return simplify_rewrite(smt_script, subaction)
        case "demod":
            return simplify_demod(smt_script, subaction)
        case "ufnorm":
            return simplify_ufnorm(
                smt_script, subaction, axioms_only=dash_suffix != ["rewrite"]
            )
        case "bitwise":
            return simplify_bitwise(smt_script, subaction)
        case "mod_inv":
            return simplify_mod_inv(smt_script, subaction)
        case "normalize":
            return simplify_normalize(smt_script, subaction)
        case "evaluator":
            return simplify_evaluate(smt_script, subaction)
        case "skolem":
            return simplify_skolem(smt_script, subaction)
        case "intervals":
            return simplify_intervals(smt_script, subaction)
        case "intervals2":
            return simplify_intervals2(smt_script, subaction)
        case "cvc5":
            return simplify_cvc5(smt_script, subaction)
        case "z3":
            return simplify_z3(smt_script, dash_suffix, subaction)
        case "model":
            return simplify_model(smt_script, subaction)
        case "isqf":
            subaction += {"expected": "qf"}
            if not check_isqf(smt_script):
                logging.warning("formula is not quantifier-free")
                subaction += {"result": "not-qf"}
            else:
                subaction += {"result": "qf"}
            return smt_script
        case "domain_probe":
            return simplify_domain_probe(smt_script, subaction)
        case "pretty" | "p":
            ARGS().pretty = True
            return smt_script
        case _:
            logging.error(f"ignoring unknown tactic: {parts.raw()}")
            return smt_script


def _ensure_declarations_for_asserts(smt_script: script.SmtLibScript) -> None:
    """Declare any symbol free in an assert but absent from declare-fun (parser else yields str)."""
    fvo = get_env().fvo
    declared: set[str] = set()
    for cmd in smt_script.commands:
        if cmd.name == "declare-fun":
            declared.add(cmd.args[0].symbol_name())
    missing: dict[str, FNode] = {}
    for cmd in smt_script.commands:
        if cmd.name != "assert":
            continue
        for sym in fvo.get_free_variables(cmd.args[0]):
            if not sym.is_symbol():
                continue
            n = sym.symbol_name()
            if n not in declared:
                missing.setdefault(n, sym)
    if not missing:
        return
    try:
        first_assert = next(
            i for i, c in enumerate(smt_script.commands) if c.name == "assert"
        )
    except StopIteration:
        return
    decls = [
        script.SmtLibCommand(name="declare-fun", args=[missing[k]])
        for k in sorted(missing)
    ]
    smt_script.commands = (
        smt_script.commands[:first_assert]
        + decls
        + smt_script.commands[first_assert:]
    )


def simplify_smt_script(
    smt_script: script.SmtLibScript | None,
    *,
    tactic: str,
    timeout: float,
    output: Path | None = None,
    parent_action: Action | None = None,
    optimization_step: str | None = None,
    input_path: Path | None = None,
) -> tuple[script.SmtLibScript | None, bool]:
    """Run colon-separated tactics. Returns ``(script, wrote_final_output)``."""
    parent = parent_action or Action("simplify-programmatic")
    groups = _pipeline_groups(tactic, optimization_step)
    deadline = time.monotonic() + float(timeout)
    step_index = 0
    wrote_final_output = False
    defer_input = input_path is not None and smt_script is None
    for group_idx, (executor, raw_list) in enumerate(groups):
        match executor:
            case "p":
                if smt_script is None:
                    assert input_path is not None
                    smt_script = _load_script(input_path)
                smt_script, step_index = _run_python_passes(
                    parent,
                    smt_script,
                    raw_list,
                    deadline=deadline,
                    output=output,
                    step_index=step_index,
                    dump_steps=getattr(ARGS(), "dump_steps", False),
                )
            case "r":
                step_end = step_index + len(raw_list)
                remaining = deadline - time.monotonic() - 2
                batch_label = ":".join(raw_list)

                if remaining <= 0:
                    for raw_tactic in raw_list:
                        step_index += 1
                        logging.info(
                            "skipping simplifier pass %s (no time budget)", raw_tactic
                        )
                        with parent.action(raw_tactic) as subaction:
                            subaction += {"result": "skipped", "reason": "no-budget"}
                    continue

                logging.info("simplifying with rust batch %s", batch_label)

                batch_input_path = input_path if defer_input else None
                defer_input = False
                rust_out: Path | None = None
                temp_out: Path | None = None
                parse_output = True
                if batch_input_path is not None:
                    if group_idx < len(groups) - 1:
                        fd, temp_name = tempfile.mkstemp(suffix=".smt2")
                        os.close(fd)
                        temp_out = Path(temp_name)
                        rust_out = temp_out
                    elif output is not None:
                        rust_out = output
                        parse_output = False
                        wrote_final_output = True

                try:
                    smt_script = _run_rust_tactics(
                        parent,
                        smt_script,
                        raw_list,
                        timeout=remaining,
                        profile_input=getattr(ARGS(), "input", None) or input_path or output,
                        profile_output=output,
                        input_path=batch_input_path,
                        rust_output_path=rust_out,
                        dump_steps_output=output,
                        dump_step_offset=step_index,
                        parse_output=parse_output,
                    )
                finally:
                    if temp_out is not None and temp_out.is_file():
                        temp_out.unlink()

                if smt_script is not None:
                    _ensure_declarations_for_asserts(smt_script)
                step_index = step_end

    if smt_script is not None:
        _ensure_declarations_for_asserts(smt_script)
    return smt_script, wrote_final_output


def simplify():
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""

    optimization_step = ARGS().optimization_step

    if stats_enabled():
        init_stats_run(wipe=False)
        set_stats_tag(getattr(ARGS(), "stats_tag", None) or stats_tag_from_path(ARGS().input))

    groups = _pipeline_groups(ARGS().tactic, optimization_step)
    rust_first = bool(groups and groups[0][0] == "r")

    with Action("simplifier") as action:
        action += {
            "inputs": [ARGS().input],
            "outputs": [ARGS().output],
            "tactic": ARGS().tactic,
            "default_executor": ARGS().default_executor,
        }
        if optimization_step:
            action += {"optimization_step": optimization_step}
        smt_script: script.SmtLibScript | None = None
        if not rust_first:
            with action.action("load"):
                smt_script = _load_script(ARGS().input)
        else:
            logging.info("deferring parse; forwarding %s to rust", ARGS().input)

        smt_script, wrote_final_output = simplify_smt_script(
            smt_script,
            tactic=ARGS().tactic,
            timeout=float(ARGS().timeout),
            output=ARGS().output,
            parent_action=action,
            optimization_step=optimization_step,
            input_path=ARGS().input if rust_first else None,
        )
        if not wrote_final_output:
            with action.action("dump"):
                with open_file(ARGS().output, "w") as out:
                    logging.info(f"dumping formula to {out.name}")
                    write_smtlib_script(smt_script, out)
        return action
