from ..rewriter import rewrite
from .conversion import FormulaWithAxioms, SmtConverter
from .utils import *

def collect_variables(data: FormulaWithAxioms) -> frozenset[FNode]:
    return frozenset.union(
        *[f.get_free_variables() for f in data.constraints],
        *[f.get_free_variables() for f in data.bus_interactions],
        *[f.get_free_variables() for f in data.axioms],
        *[f.get_free_variables() for f in data.derived],
    )

def build_vc(f1: FormulaWithAxioms, f2: FormulaWithAxioms) -> FNode:

    var1 = collect_variables(f1)
    var2 = collect_variables(f2)

    globals = f1.globals | f2.globals

    onlyfirst = (var1 - var2) - globals

    f = ForAll(onlyfirst,
        And(
            Not(Iff(
                And(*f1.constraints, *f1.bus_interactions),
                And(*f2.constraints, *f2.bus_interactions)
            )),
            And(*f1.axioms),
            And(*f2.axioms),
            And(*f1.derived),
            And(*f2.derived),
        )
    )
    return rewrite(f)
