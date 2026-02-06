from .conversion import FormulaWithAxioms
from .utils import *

def collect_variables(data: FormulaWithAxioms) -> frozenset[FNode]:
    """Collect all free variables that appear anywhere in a `FormulaWithAxioms`."""
    return frozenset.union(
        *[f.get_free_variables() for f in data.constraints],
        *[f.get_free_variables() for f in data.bus_interactions],
        *[f.get_free_variables() for f in data.axioms],
        *[f[1].get_free_variables() for f in data.derived],
    )

def build_input_output_relation(name: str, a: dict, b: dict) -> FNode:
    """Build a conjunction equating shared input/output symbols between two encodings."""
    keys = a.keys() & b.keys()
    return And(
        *[
            with_comment(
                And(Equals(x, y) for x,y in zip(a[k], b[k])),
                f"{name} for {k}"
            )
            for k in keys
        ],
    )
