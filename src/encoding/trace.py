"""Trace encoding: satisfiable core formula and unsat sanity obligations."""
import itertools
from ..smt.conversion import FormulaWithAxioms, SmtConverter
from ..smt.utils import *
from .utils import as_script

from .sanity import sanity_mult_values, sanity_satisfies_derived, sanity_stateful_mult_pairs, sanity_timestamps_increase

@as_script("sat")
def encode_trace(formula: FormulaWithAxioms) -> script.SmtLibScript:
    return And(*formula.constraints, *formula.axioms)

@as_script("unsat")
def encode_trace_sanity(conv: SmtConverter, formula: FormulaWithAxioms) -> script.SmtLibScript:
    """
    Checks validity of
    Forall(vars,
        Implies(
            And(*constraints, *axioms),
            And(*sanity_checks)
        )
    )

    reformulated as checking unsat of
        And(
            *constraints,
            *axioms,
            Not(And(*sanity_checks))
        )


    """
    checks = itertools.chain(
        sanity_satisfies_derived(formula),
        sanity_mult_values(conv, formula),
        sanity_stateful_mult_pairs(conv, formula),
        #sanity_timestamps_increase(conv, formula),
    )
    return And(
        *formula.constraints,
        *formula.axioms,
        Or(*checks),
    )

