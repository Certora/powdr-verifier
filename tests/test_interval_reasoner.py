from src.rewriter import rewrite_intervals
from src.rewriter.interval_reasoner import IntervalReasoner
from src.smt.utils import *


def _has_mod(f: FNode) -> bool:
    if f.is_mod():
        return True
    return any(_has_mod(a) for a in f.args())


def test_recognize_inequalities_and_or_equalities():
    x = Symbol("x", INT)
    assumptions = [
        LE(Int(0), x),
        LT(x, Int(10)),
        Or(Equals(x, Int(2)), Equals(x, Int(3)), Equals(x, Int(4))),
    ]
    r = IntervalReasoner()
    r.assume_all(assumptions)
    iv = r.get_interval(x)
    assert iv.lo == 2
    assert iv.hi == 4


def test_mod_no_overflow_only_for_canonical_range():
    p = int(ARGS().field_type.value)
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    assumptions = [LE(Int(0), a), LE(a, Int(100)), LE(Int(0), b), LE(b, Int(100))]

    # safe: a is canonical
    out = rewrite_intervals([Mod(a, Int(p))], assumptions=assumptions)[0]
    assert not _has_mod(out)

    # unsafe: a-b can be negative, keep mod
    out2 = rewrite_intervals([Mod(a - b, Int(p))], assumptions=assumptions)[0]
    assert _has_mod(out2)


def test_used_constraints_are_retained_under_pruning():
    x = Symbol("x", INT)
    assumptions = [Equals(x, Int(0))]
    out = rewrite_intervals(
        [Equals(x, Int(0))],
        assumptions=assumptions,
        prune=True,
    )[0]
    # Without retention this would simplify to True under pruning.
    assert out == Equals(x, Int(0))


def test_bound_deriving_formula_is_not_eliminated():
    x = Symbol("x", INT)
    bound = LE(x, Int(10))
    # Non-critical tautology that can be dropped under pruning.
    redundant = Equals(Int(1), Int(1))

    out = rewrite_intervals(
        [bound, redundant],
        assumptions=[bound, redundant],
        prune=True,
    )

    # `bound` was used to derive x <= 10, so it must be kept verbatim.
    assert out[0] == bound
    # `redundant` was not needed and is not a field-bound guard; pruning may collapse it.
    assert out[1].is_true()


def test_field_bounds_0_and_p_are_not_eliminated():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)

    lower = LE(Int(0), x)
    upper = LT(x, Int(p))

    out = rewrite_intervals(
        [lower, upper],
        assumptions=[lower, upper],
        prune=True,
    )

    assert out[0] == lower
    assert out[1] == upper

