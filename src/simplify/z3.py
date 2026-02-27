import z3

from .utils import convert_script_to_string

@convert_script_to_string
def simplify_z3(smt: str) -> str:
    tactics = ("simplify", "propagate-values", "simplify")
    query = z3.parse_smt2_string(smt)
    goal = z3.Goal()
    goal.add(query)
    simplified = z3.Then(*tactics)(goal).as_expr()
    solver = z3.Solver()
    solver.add(simplified)
    return solver.sexpr()
