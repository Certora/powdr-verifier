"""Range-check activity evidence: the indexed proportionality search.

``_range_mult_evidence`` proves a range-check row is SENT before its range is
allowed to bound anything. When the multiplicity's residual is symbolic, the
proof is a constraint whose column part is proportional to that residual. The
candidates are found through ``_constraints_by_support`` rather than by scanning
every constraint; these tests pin the outcome for both lookup branches (subset
enumeration and the degenerate index walk) and for a disabled row.
"""
import pytest

from src.membus.busmodel import VAR_RANGE
from src.membus.rules import Analysis

FLAG_A = "flag_a"
FLAG_B = "flag_b"
PIN_A = "pin_a"
PIN_B = "pin_b"
VAL = "value_col"


def _sum(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


def _dump(mult, extra_constraints=()):
    """A VAR_RANGE row on ``VAL`` gated by ``mult``, plus flag constraints."""
    return {
        "bus_interactions": [
            {"id": VAR_RANGE, "mult": mult, "args": [VAL, 8]},
        ],
        "constraints": [
            _sum(FLAG_A, FLAG_B, -1),          # 0: flag_a + flag_b = 1  (nonzero)
            *extra_constraints,
        ],
    }


def _bound_of(data, col=VAL):
    return Analysis(data, assume_is_valid=False)._static_bounds.get(col)


def test_symbolic_residual_proved_by_proportional_constraint():
    """``mult = flag_a + flag_b`` is nonzero by constraint 0, so the row bounds."""
    b = _bound_of(_dump(_sum(FLAG_A, FLAG_B)))
    assert b is not None and (b.lo, b.hi) == (0, 1 << 8)
    # The citation names the proving constraint, not just the bus row.
    assert ("constraint", 0) in [(s.kind, s.index) for s in b.sources]


def test_unprovable_residual_bounds_nothing():
    """No constraint pins ``flag_a`` alone ⟹ activity unproven ⟹ no bound."""
    assert _bound_of(_dump(FLAG_A)) is None


def test_disabled_row_bounds_nothing():
    """``mult`` folds to 0 through the const pins ⟹ the row is disabled."""
    data = _dump(PIN_A, extra_constraints=[PIN_A])   # pin_a = 0
    assert _bound_of(data) is None


@pytest.mark.parametrize("pins", [1, 2, 3, 4])
def test_pinned_columns_do_not_hide_the_evidence(pins):
    """``mult = flag_a + flag_b + Σ pinned`` still resolves.

    The pinned columns are folded out of the residual, so the proving constraint
    (support ``{flag_a, flag_b}``) has to be found under a support that differs
    from the raw multiplicity's. With few pins the lookup enumerates subsets of
    the pinned set; as the pin count passes the number of distinct supports in
    the (tiny) machine it switches to walking the index. Both must agree.
    """
    pin_cols = [f"pin_{i}" for i in range(pins)]
    mult = _sum(FLAG_A, FLAG_B, *pin_cols)
    # Each pin_i = 0 via its own single-column constraint (so it is substituted
    # out and cited), leaving the residual flag_a + flag_b.
    b = _bound_of(_dump(mult, extra_constraints=list(pin_cols)))
    assert b is not None and (b.lo, b.hi) == (0, 1 << 8)
    assert ("constraint", 0) in [(s.kind, s.index) for s in b.sources]
