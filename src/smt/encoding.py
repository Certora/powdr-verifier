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
    """Build a conjunction equating input/output symbols between two encodings.

    Iterates every bus key declared on either side; for each key present in
    both dicts, emit pairwise equalities between the two symbol lists.
    """
    keys = sorted(a.keys() | b.keys(), key=str)

    def equals(x: FNode, y: FNode) -> FNode:
        if x.get_type().is_int_type() and y.get_type().is_int_type():
            return Equals(wrap_mod(Minus(x, y)), Int(0))
        else:
            return Equals(x, y)

    parts = []
    for k in keys:
        va, vb = a.get(k), b.get(k)
        if va is None or vb is None:
            continue
        parts.append(
            with_comment(
                And(equals(x, y) for x, y in zip(va, vb)), f"{name} for {k}"
            )
        )
    return And(*parts) if parts else TRUE()
