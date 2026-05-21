"""Cross-encoding variable collection and input/output equality constraints."""
from .conversion import FormulaWithAxioms
from .utils import *


def collect_variables(data: FormulaWithAxioms) -> frozenset[FNode]:
    """Collect all free variables that appear anywhere in a `FormulaWithAxioms`."""
    return frozenset.union(
        *[f.get_free_variables() for f in data.constraints],
        *[f.get_free_variables() for f in data.axioms],
        *[f.get_free_variables() for f in data.derived.values()],
    )


def build_input_output_relation(name: str, a: dict, b: dict) -> FNode:
    """Build a conjunction equating shared input/output symbols between two encodings."""
    keys = a.keys() & b.keys()
    def equals(x: FNode, y: FNode) -> FNode:
        if x.get_type().is_int_type() and y.get_type().is_int_type():
            return Equals(wrap_mod(Minus(x, y)), Int(0))
        else:
            return Equals(x, y)
    return And(
        *[
            with_comment(
                And(equals(x, y) for x, y in zip(a[k], b[k])), f"{name} for {k}"
            )
            for k in keys
        ],
    )
