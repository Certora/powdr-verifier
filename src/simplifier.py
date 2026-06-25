"""SMT-LIB simplification pipeline driven by colon-separated tactic names.

Each tactic mutates or inspects a parsed script in place; optional per-step
dumps are controlled via ``--dump-steps``. Serialization uses ``--pretty`` or
the ``pretty`` tactic (sets ``ARGS().pretty``).
"""
import copy
import logging
import signal
import time
from pathlib import Path
from typing import Callable, TypeVar

from .report.action import Action
from .smt.utils import *
from .smt_backends.pysmt import write_smtlib_script
from .utils.args import ARGS
from .utils.io import open_file

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
    simplify_z3,
)

_T = TypeVar("_T")

TACTIC_QEPREFIX = "nnf:evaluator:skolem:lift:witness:demod:z3-propagate-values:flatten_outer_array:isqf"

DEFAULT_TACTIC = (
    TACTIC_QEPREFIX + ":bounds:demod:normalize:rewrite:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod:pretty"
)

# Custom colon-separated pipelines keyed by powdr optimization pass name (e.g. ``remove_free``).
STEP_TACTICS: dict[str, str] = {
    "exec_bus": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod:pretty",
    "loop_iteration": TACTIC_QEPREFIX + ":bounds:demod:normalize:bitwise:mod_inv:demod:z3-propagate-values:normalize:demod:pretty",
    "solver": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod:pretty",
    "substitute_bus_interactio_fields": TACTIC_QEPREFIX + ":bounds:bitwise:mod_inv:demod:domain_probe:z3-propagate-values:z3-solve-eqs:normalize:demod:pretty",
}


def resolve_tactic(tactic: str, optimization_step: str | None = None) -> str:
    """Resolve ``default`` and per-step overrides to a colon-separated pipeline."""
    if tactic != "default":
        return tactic
    if optimization_step and optimization_step in STEP_TACTICS:
        return STEP_TACTICS[optimization_step]
    return DEFAULT_TACTIC


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


def _apply_tactic_pass(
    base: str,
    dash_suffix: list[str],
    smt_script: script.SmtLibScript,
    subaction,
) -> script.SmtLibScript:
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
            logging.error(f"ignoring unknown tactic: {base}")
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
    smt_script: script.SmtLibScript,
    *,
    tactic: str,
    timeout: float,
    output: Path | None = None,
    parent_action: Action | None = None,
    optimization_step: str | None = None,
) -> script.SmtLibScript:
    """Run colon-separated tactics on ``smt_script`` (mutated in place)."""
    parent = parent_action or Action("simplify-programmatic")
    resolved = resolve_tactic(tactic, optimization_step)
    tactics = resolved.split(":")
    deadline = time.monotonic() + float(timeout)
    for step_index, raw_tactic in enumerate(tactics):
        step_no = step_index + 1
        remaining = deadline - time.monotonic() - 2

        base, *dash_suffix = raw_tactic.split("-", 1)

        logging.info("simplifying with %s", raw_tactic)
        with parent.action(raw_tactic) as subaction:
            if remaining <= 0:
                logging.info("skipping simplifier pass %s (no time budget)", raw_tactic)
                subaction += {"result": "skipped", "reason": "no-budget"}
                continue

            backup_script = script.SmtLibScript()
            if smt_script.annotations is not None:
                backup_script.annotations = copy.copy(smt_script.annotations)
            backup_script.commands = [
                cmd._replace(args=list(cmd.args)) for cmd in smt_script.commands
            ]
            backup_pretty = ARGS().pretty

            def run_step():
                return _apply_tactic_pass(base, dash_suffix, smt_script, subaction)

            timed_out, step_script = _run_with_itimer(remaining, run_step)

            if timed_out:
                smt_script = backup_script
                ARGS().pretty = backup_pretty
                logging.warning("simplifier pass %s hit timeout, skipping", raw_tactic)
                subaction += {"result": "timeout"}
            else:
                assert step_script is not None
                smt_script = step_script
                _ensure_declarations_for_asserts(smt_script)

        if ARGS().dump_steps and output is not None:
            stem = output.name[: -len(output.suffix)] if output.suffix else output.name
            dump_file = output.with_name(f"{stem}.{step_no:02d}.{raw_tactic}.smt2")
            with open_file(dump_file, "w") as out:
                logging.info("dumping intermediate formula to %s", out.name)
                write_smtlib_script(smt_script, out)

    _ensure_declarations_for_asserts(smt_script)
    return smt_script


def simplify():
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""

    optimization_step = ARGS().optimization_step

    with Action("simplifier") as action:
        action += {
            "inputs": [ARGS().input],
            "outputs": [ARGS().output],
            "tactic": ARGS().tactic,
        }
        if optimization_step:
            action += {"optimization_step": optimization_step}
        with action.action("load"):
            with open_file(ARGS().input, "r") as f:
                parser = SmtLibParser()
                logging.info(f"loading from {f.name}")
                smt_script = parser.get_script(f)

        smt_script = simplify_smt_script(
            smt_script,
            tactic=ARGS().tactic,
            timeout=float(ARGS().timeout),
            output=ARGS().output,
            parent_action=action,
            optimization_step=optimization_step,
        )
        with action.action("dump"):
            with open_file(ARGS().output, "w") as out:
                logging.info(f"dumping formula to {out.name}")
                write_smtlib_script(smt_script, out)
        return action
