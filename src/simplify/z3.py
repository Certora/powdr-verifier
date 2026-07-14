"""Run Z3 tactics on the asserted fragment up to ``check-sat``, then re-emit simplified asserts."""
import logging

from ..smt_backends.pysmt import *
import z3

from ..utils.stats import stats_dump
from .utils import _string_to_script


def _declared_symbol_names(commands: list) -> set[str]:
    names: set[str] = set()
    for cmd in commands:
        if cmd.name == "declare-fun":
            names.add(cmd.args[0].symbol_name())
    return names


def _declares_from_z3_not_in_prefix(
    processed: list, prefix_names: set[str]
) -> list:
    out: list = []
    seen = set(prefix_names)
    for cmd in processed:
        if cmd.name != "declare-fun":
            continue
        sym = cmd.args[0]
        n = sym.symbol_name()
        if n in seen:
            continue
        seen.add(n)
        out.append(cmd)
    return out


def _mk_tactic(t: str):
    """Tactic by name, with parameterized variants.

    ``solve-eqs-nomod`` = ``(using-params solve-eqs :eliminate_mod false)``:
    disables ``solve_mod`` (z3 ``extract_eqs.cpp:233``), the rewrite
    ``(= (mod u P) y) => u := P*mod!k + y`` that mints the ``mod!``
    quotient witnesses goal-wide — including inside uf arguments.
    """
    if t == "solve-eqs-nomod":
        return z3.With("solve-eqs", eliminate_mod=False)
    return z3.Tactic(t)


def simplify_z3(
    smt_script: script.SmtLibScript, args: list, subaction=None
) -> script.SmtLibScript:
    """Feed asserts to a Z3 ``Tactic`` solver until ``check-sat``, then splice back simplified asserts."""
    match args:
        case []:
            tactic = z3.Repeat(
                z3.Then(
                    "propagate-values",
                    "elim-term-ite",
                    "propagate-ineqs",
                    "solve-eqs",
                    "ctx-simplify",
                )
            )
        case [t]:
            tactic = _mk_tactic(t)
        case [*t]:
            tactic = z3.Then(*[_mk_tactic(x) for x in t])

    s = tactic.solver()
    conv = Z3Converter(get_env(), s.ctx)

    prefix: list = []
    suffix: list = []
    in_suffix = False
    output: list = []
    z3_asserts_in = 0

    for cmd in smt_script:
        if in_suffix:
            suffix.append(cmd)
            continue
        match cmd.name:
            case "set-info" | "set-logic" | "set-option" | "declare-fun" | "get-model" | "get-unsat-core" | "echo":
                prefix.append(cmd)
            case "assert":
                z3_asserts_in += 1
                s.add(conv.convert(cmd.args[0]))
            case "check-sat":
                z3_check = s.check()
                processed = _string_to_script(s.sexpr()).commands
                prefix_names = _declared_symbol_names(prefix)
                extra_decls = _declares_from_z3_not_in_prefix(
                    processed, prefix_names
                )
                new_asserts = [
                    c for c in processed
                    if c.name == "assert" and not c.args[0].is_true()
                ]
                output = list(prefix) + extra_decls + new_asserts + [cmd]
                in_suffix = True
                stats_dump(
                    "z3",
                    {
                        "backend": "python",
                        "z3_check": str(z3_check),
                        "asserts_in": z3_asserts_in,
                        "asserts_out": len(new_asserts),
                        "extra_declarations": len(extra_decls),
                        "tactic_args": list(args) if args else None,
                    },
                )
            case _:
                assert False, f"unexpected command: {cmd.name}"

    res = script.SmtLibScript()
    res.commands = output + suffix
    return res
