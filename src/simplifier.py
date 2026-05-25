"""SMT-LIB simplification pipeline driven by colon-separated tactic names.

Each tactic mutates or inspects a parsed script in place; optional per-step
dumps are controlled via ``--dump-steps``; final serialization uses ``--pretty``
(or the ``pretty`` tactic, which sets that flag on ``ARGS()``).
"""
import copy
import logging
import signal
import time
from typing import Callable, TypeVar

from .report.action import Action
from .smt.utils import *
from .smt_backends.pysmt import pretty_print_smtlib, serialize_smtlib
from .utils.args import ARGS
from .utils.io import open_file

from .simplify.witness import simplify_witnesses
from .simplify.domain_probe import simplify_domain_probe
from .simplify import (
    check_isqf,
    simplify_andify,
    simplify_array_subst,
    simplify_bounds,
    simplify_cvc5,
    simplify_demod,
    simplify_evaluate,
    simplify_gxor,
    simplify_intervals,
    simplify_intervals2,
    simplify_isolate,
    simplify_lift_forall,
    simplify_mod_inv,
    simplify_model,
    simplify_nnf,
    simplify_qxor,
    simplify_rewrite,
    simplify_skolem,
    simplify_z3,
)

_T = TypeVar("_T")


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
            return simplify_witnesses(smt_script)
        case "array_subst":
            return simplify_array_subst(smt_script)
        case "andify":
            return simplify_andify(smt_script)
        case "bounds":
            return simplify_bounds(smt_script)
        case "nnf":
            return simplify_nnf(smt_script)
        case "isolate":
            return simplify_isolate(smt_script)
        case "lift":
            return simplify_lift_forall(smt_script)
        case "rewrite":
            return simplify_rewrite(smt_script)
        case "demod":
            return simplify_demod(smt_script)
        case "qxor":
            return simplify_qxor(smt_script)
        case "gxor":
            return simplify_gxor(smt_script)
        case "mod_inv":
            return simplify_mod_inv(smt_script)
        case "evaluator":
            return simplify_evaluate(smt_script)
        case "skolem":
            return simplify_skolem(smt_script)
        case "intervals":
            return simplify_intervals(smt_script)
        case "intervals2":
            return simplify_intervals2(smt_script)
        case "cvc5":
            return simplify_cvc5(smt_script)
        case "z3":
            return simplify_z3(smt_script, dash_suffix)
        case "model":
            return simplify_model(smt_script)
        case "isqf":
            subaction += {"expected": "qf"}
            if not check_isqf(smt_script):
                logging.warning("formula is not quantifier-free")
                subaction += {"result": "not-qf"}
            else:
                subaction += {"result": "qf"}
            return smt_script
        case "domain_probe":
            return simplify_domain_probe(smt_script)
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


def simplify():
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""

    with Action("simplifier") as action:
        action += {
            "inputs": [ARGS().input],
            "outputs": [ARGS().output],
        }
        with action.action("load"):
            with open_file(ARGS().input, "r") as f:
                parser = SmtLibParser()
                logging.info(f"loading from {f.name}")
                smt_script = parser.get_script(f)

        tactics = ARGS().tactic.split(":")
        deadline = time.monotonic() + float(ARGS().timeout)

        for step_index, raw_tactic in enumerate(tactics):
            step_no = step_index + 1
            remaining = deadline - time.monotonic() - 2

            base, *dash_suffix = raw_tactic.split("-", 1)

            logging.info(f"simplifying with {raw_tactic}")
            with action.action(raw_tactic) as subaction:
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

            if ARGS().dump_steps:
                output = ARGS().output
                stem = output.name[:-len(output.suffix)] if output.suffix else output.name
                dump_file = output.with_name(f"{stem}.{step_no:02d}.{raw_tactic}.smt2")
                with open_file(dump_file, "w") as out:
                    logging.info(f"dumping intermediate formula to {out.name}")
                    if ARGS().pretty:
                        pretty_print_smtlib(smt_script, out)
                    else:
                        serialize_smtlib(smt_script, out)

        _ensure_declarations_for_asserts(smt_script)
        with action.action("dump"):
            with open_file(ARGS().output, "w") as out:
                logging.info(f"dumping formula to {out.name}")
                if ARGS().pretty:
                    pretty_print_smtlib(smt_script, out)
                else:
                    serialize_smtlib(smt_script, out)
        return action
