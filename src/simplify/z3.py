from io import StringIO
from ..smt_backends.pysmt import *
import z3

from .utils import _string_to_script

def simplify_z3(smt_script: script.SmtLibScript, args = []) -> script.SmtLibScript:

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
            tactic = z3.Tactic(t)
        case [*t]:
            tactic = z3.Then(*t)

    s = tactic.solver()
    conv = Z3Converter(get_env(), s.ctx)

    output = []

    in_suffix = False
    for cmd in smt_script:
        if in_suffix:
            output.append(cmd)
            continue
        match cmd.name:
            case "set-info" | "set-logic" | "set-option" | "get-model" | "get-unsat-core" | "echo":
                output.append(cmd)
            case "declare-fun":
                #output.append(cmd)
                #decls[cmd.args[0].symbol_name()] = conv.walk_symbol(cmd.args[0])
                pass
            case "assert":
                s.add(conv.convert(cmd.args[0]))
            case "check-sat":
                s.check()
                output += _string_to_script(s.sexpr()).commands
                output.append(cmd)
                in_suffix = True
            case _:
                assert False, f"unexpected command: {cmd.name}"
    
    res = script.SmtLibScript()
    res.commands = output
    return res
