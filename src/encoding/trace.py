from ..smt.conversion import FormulaWithAxioms
from ..smt.utils import *
from .utils import as_script

@as_script("sat")
def encode_trace(formula: FormulaWithAxioms) -> script.SmtLibScript:
    return And(*formula.constraints, *formula.axioms)

@as_script("unsat")
def encode_trace_satisfies_derived(formula: FormulaWithAxioms) -> script.SmtLibScript:
    return And(
        *formula.constraints,
        *formula.axioms,
        Or(
            *[Not(Equals(v, expr)) for v, expr in formula.derived.items()]
        ),
    )

