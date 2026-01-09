from .smt import *

def collect_variables(data: FormulaWithAxioms) -> frozenset[FNode]:
    return (
        data.formula.get_free_variables() |
        data.axioms.get_free_variables() |
        data.derived.get_free_variables()
    )

def build_vc(f1: FormulaWithAxioms, f2: FormulaWithAxioms) -> FNode:

    var1 = collect_variables(f1)
    var2 = collect_variables(f2)

    onlyfirst = var1 - var2

    f = ForAll(onlyfirst,
        And(
            Not(Iff(f1.formula, f2.formula)),
            f1.axioms,
            f2.axioms,
            f1.derived,
            f2.derived,
        )
    )
    return rewrite(f)
