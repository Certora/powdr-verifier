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

def build_input_output_relation(name: str, a: dict, b: dict) -> FNode:
    keys = a.keys() & b.keys()
    return And(
        *[
            with_comment(
                And(Equals(x, y) for x in a[k] for y in b[k]),
                f"{name} for {k}"
            )
            for k in keys
        ],
    )

def build_vc(f1: FormulaWithAxioms, c1: SmtConverter, f2: FormulaWithAxioms, c2: SmtConverter) -> FNode:

    inputs1 = c1.bus_interaction_encoder.get_inputs()
    inputs2 = c2.bus_interaction_encoder.get_inputs()
    outputs1 = c1.bus_interaction_encoder.get_outputs()
    outputs2 = c2.bus_interaction_encoder.get_outputs()

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
            build_input_output_relation("INPUT RELATION", inputs1, inputs2),
            build_input_output_relation("OUTPUT RELATION", outputs1, outputs2),
        )
    )
    return rewrite(f)
