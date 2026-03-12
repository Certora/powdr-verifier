from src.simplify.intervals import IntervalReasoner
from src.smt.utils import *


def _has_mod(f: FNode) -> bool:
    if f.is_mod():
        return True
    return any(_has_mod(a) for a in f.args())


def _simplify_with_intervals(
    input_formulas: list[FNode],
    *,
    assumptions: list[FNode],
    prune: bool = True,
) -> list[FNode]:
    reasoner = IntervalReasoner(modulus=ARGS().field_type.value)
    reasoner.assume_all(assumptions)
    protected = set(reasoner.used_formulas)
    protected |= {f for f in input_formulas if reasoner.must_retain_formula(f)}
    return [
        reasoner.simplify(f, prune=prune, freeze=protected, inject_quantifier_bounds=True)
        for f in input_formulas
    ]


def test_interval_refinement_from_simple_inequalities():
    x = Symbol("x", INT)
    r = IntervalReasoner()
    r.assume_all([LE(Int(0), x), LT(x, Int(16))])
    iv = r.get_interval(x)
    assert iv.lo == 0
    assert iv.hi == 15


def test_eval_bool_with_arithmetic_product_bounds():
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    r = IntervalReasoner()
    r.assume_all(
        [
            LE(Int(0), x),
            LE(x, Int(3)),
            LE(Int(0), y),
            LE(y, Int(4)),
        ]
    )

    # x*y in [0, 12]
    assert r.eval_bool((x * y) <= Int(12)) is True
    assert r.eval_bool((x * y) < Int(0)) is False
    assert r.eval_bool(Equals(x * y, Int(7))) is None


def test_eval_bool_with_addition_and_subtraction():
    a = Symbol("a", INT)
    b = Symbol("b", INT)
    r = IntervalReasoner()
    r.assume_all(
        [
            LE(Int(10), a),
            LE(a, Int(20)),
            LE(Int(3), b),
            LE(b, Int(5)),
        ]
    )

    # (a - b) in [5, 17]
    assert r.eval_bool((a - b) >= Int(5)) is True
    assert r.eval_bool((a - b) < Int(5)) is False
    assert r.eval_bool(Equals(a + b, Int(18))) is None


def test_simplify_intervals_removes_mod_when_no_overflow():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    assumptions = [LE(Int(0), x), LE(x, Int(100))]

    out = _simplify_with_intervals([Mod(x, Int(p))], assumptions=assumptions)[0]
    assert not _has_mod(out)
    assert out == x


def test_simplify_intervals_keeps_mod_when_negative_possible():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    assumptions = [
        LE(Int(0), x),
        LE(x, Int(100)),
        LE(Int(0), y),
        LE(y, Int(100)),
    ]

    out = _simplify_with_intervals([Mod(x - y, Int(p))], assumptions=assumptions)[0]
    assert _has_mod(out)


def test_mod_zero_to_eq_zero_in_injective_window():
    p = int(ARGS().field_type.value)
    x = Symbol("x", INT)
    assumptions = [LE(Int(-5), x), LE(x, Int(5))]

    f = Equals(Mod(x, Int(p)), Int(0))
    out = _simplify_with_intervals([f], assumptions=assumptions)[0]
    assert out == Equals(x, Int(0))

