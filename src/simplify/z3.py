from io import StringIO
from pysmt.smtlib import script
import z3

from .utils import _string_to_script

def simplify_z3(smt_script: script.SmtLibScript, args = []) -> script.SmtLibScript:
    prefix = []
    main = []
    suffix = []
    before = True
    for cmd in smt_script:
        s = cmd.serialize_to_string(daggify=False)
        match cmd.name:
            case "assert" | "declare-fun" | "define-fun":
                before = False
                main.append(s)
            case _:
                if before:
                    prefix.append(s)
                else:
                    suffix.append(s)
    
    match args:
        case []:
            tactic = z3.Repeat(
                z3.Then(
                    z3.Repeat(z3.Then("simplify", "propagate-values", "solve-eqs")),
                    "ctx-simplify",
                    "propagate-ineqs",
                )
            )
        case [t]:
            tactic = z3.Tactic(t)
        case [*t]:
            tactic = z3.Then(*t)

    query = z3.parse_smt2_string("\n".join(main))
    goal = z3.Goal()
    goal.add(query)
    simplified = tactic(goal).as_expr()
    solver = z3.Solver()
    solver.add(simplified)
    res = solver.sexpr()

    return _string_to_script("\n".join(prefix + [res] + suffix))

