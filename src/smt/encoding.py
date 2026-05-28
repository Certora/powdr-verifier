"""Cross-encoding variable collection."""
from .conversion import FormulaWithAxioms
from .utils import *


def collect_variables(data: FormulaWithAxioms) -> frozenset[FNode]:
    """Collect all free variables that appear anywhere in a `FormulaWithAxioms`."""
    return frozenset.union(
        *[f.get_free_variables() for f in data.constraints],
        *[f.get_free_variables() for f in data.axioms],
        *[f.get_free_variables() for f in data.derived.values()],
    )
