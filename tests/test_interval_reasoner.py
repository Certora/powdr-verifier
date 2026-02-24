from src.rewriter import rewrite_intervals
from src.rewriter.interval_reasoner import IntInterval, IntervalReasoner
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


def test_rewrite_intervals_can_append_derived_ranges():
    x = Symbol("x", INT)
    assumptions = [LE(Int(0), x), LE(x, Int(10))]
    out = rewrite_intervals(
        [Equals(Int(1), Int(1))],
        assumptions=assumptions,
        prune=True,
        append_derived_ranges=True,
    )

    # Original (simplified) formula is preserved, plus inferred range constraints.
    assert len(out) >= 2
    assert out[0].is_true()
    expected_range = And(LE(Int(0), x), LE(x, Int(10)))
    assert any(c == expected_range for c in out[1:])


def test_fixed_point_opcode_flags_sum_forces_all_zero():
    sub = Symbol("sub", INT)
    xor = Symbol("xor", INT)
    orf = Symbol("orf", INT)
    andf = Symbol("andf", INT)

    assumptions = [
        Or(Equals(sub, Int(0)), Equals(sub, Int(1))),
        Or(Equals(xor, Int(0)), Equals(xor, Int(1))),
        Or(Equals(orf, Int(0)), Equals(orf, Int(1))),
        Or(Equals(andf, Int(0)), Equals(andf, Int(1))),
        Equals(sub + Int(2) * xor + Int(3) * orf + Int(4) * andf, Int(0)),
    ]

    r = IntervalReasoner()
    r.assume_all(assumptions)

    assert r.get_interval(sub) == IntInterval.const(0)
    assert r.get_interval(xor) == IntInterval.const(0)
    assert r.get_interval(orf) == IntInterval.const(0)
    assert r.get_interval(andf) == IntInterval.const(0)


def test_fixed_point_requires_mod_elimination_before_affine_sum():
    p = int(ARGS().field_type.value)
    sub = Symbol("sub2", INT)
    xor = Symbol("xor2", INT)
    orf = Symbol("orf2", INT)
    andf = Symbol("andf2", INT)

    # First, derive each flag in [0,1]. Only then the mod-equation can be
    # normalized to a plain affine equality (sum in [0,10] < p).
    assumptions = [
        Or(Equals(sub, Int(0)), Equals(sub, Int(1))),
        Or(Equals(xor, Int(0)), Equals(xor, Int(1))),
        Or(Equals(orf, Int(0)), Equals(orf, Int(1))),
        Or(Equals(andf, Int(0)), Equals(andf, Int(1))),
        Equals(Mod(sub + Int(2) * xor + Int(3) * orf + Int(4) * andf, Int(p)), Int(0)),
    ]

    r = IntervalReasoner(modulus=p)
    r.assume_all(assumptions)

    assert r.get_interval(sub) == IntInterval.const(0)
    assert r.get_interval(xor) == IntInterval.const(0)
    assert r.get_interval(orf) == IntInterval.const(0)
    assert r.get_interval(andf) == IntInterval.const(0)


def test_mod_zero_rewrites_to_unique_nonzero_multiple():
    p = int(ARGS().field_type.value)
    x = Symbol("x_unique_mult", INT)
    assumptions = [LE(Int(p - 2), x), LE(x, Int(p + 3))]

    f = Equals(Mod(x, Int(p)), Int(0))
    out = rewrite_intervals([f], assumptions=assumptions, prune=False)[0]

    assert out == Equals(x, Int(p))


def test_constraints_5_and_6_style_mods_are_removed():
    p = int(ARGS().field_type.value)
    f0 = Symbol("f0", INT)
    f1 = Symbol("f1", INT)
    f2 = Symbol("f2", INT)
    f3 = Symbol("f3", INT)
    flag_sum = f0 + f1 + f2 + f3

    assumptions = [
        Or(Equals(f0, Int(0)), Equals(f0, Int(1)), Equals(f0, Int(2))),
        Or(Equals(f1, Int(0)), Equals(f1, Int(1)), Equals(f1, Int(2))),
        Or(Equals(f2, Int(0)), Equals(f2, Int(1)), Equals(f2, Int(2))),
        Or(Equals(f3, Int(0)), Equals(f3, Int(1)), Equals(f3, Int(2))),
    ]

    constraint_5_like = Or(
        Equals(flag_sum, Int(0)),
        Equals(Mod(Int(p - 2) + flag_sum, Int(p)), Int(0)),
        Equals(Mod(Int(p - 1) + flag_sum, Int(p)), Int(0)),
    )
    constraint_6_like = Or(
        Equals(Mod(Int(p - 2) + flag_sum, Int(p)), Int(0)),
        Equals(Mod(Int(p - 1) + flag_sum, Int(p)), Int(0)),
    )

    out = rewrite_intervals(
        [constraint_5_like, constraint_6_like],
        assumptions=assumptions,
        prune=False,
    )

    assert all(not _has_mod(f) for f in out)

