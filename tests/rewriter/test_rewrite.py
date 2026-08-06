"""Entry-point tests for `rewrite`: what it does, and what it deliberately leaves alone.

The two tests this file used to hold asserted a contract `rewrite` no longer has --
folding a linear form (`512 + ... - 512`, `a * 0`) and solving a congruence
`(a - b) mod P = 0` down to `a = b`. Both moved to their own passes and are tested
there (`tests/simplify/test_normalize.py`, `tests/simplify/test_solve_eqs.py`), so
`rewrite` returned those inputs untouched and the tests had been failing ever since.

What `rewrite` owns now is the modular-product split, checked here at the `rewrite()`
entry point (`test_rewrite_choice.py` covers the inner `rewrite_choice_simple`
exhaustively over small values).
"""
from src.rewriter import rewrite
from src.smt.utils import *
from src.utils.args import ARGS, parse_args


def _p() -> int:
    parse_args(["check", "x"])
    return ARGS().field_type.value


def _truth(f: FNode, assignment: dict[FNode, FNode]) -> bool:
    """Ground ``f`` under ``assignment`` and read off its truth value."""
    g = f.substitute(assignment).simplify()
    assert g.is_bool_constant(), f"not ground: {g}"
    return g.is_true()


def _agree_on(f: FNode, g: FNode, points: list[dict[FNode, FNode]]) -> None:
    for point in points:
        assert _truth(f, point) == _truth(g, point), (
            f"disagree at {[(str(k), str(v)) for k, v in point.items()]}: {f} vs {g}"
        )


def test_rewrite_splits_booleanity_into_roots_and_range():
    """`x(x-1) = 0 mod P` -> the root disjunction plus the interval it implies.

    The range conjuncts are redundant given the disjunction but hand the solver
    directly propagatable bounds; both are asserted so a change to either is visible.
    """
    p = _p()
    x = Symbol("x", INT)
    out = rewrite(Equals(wrap_mod(Times(x, Plus(x, Int(p - 1)))), Int(0)))

    assert out == And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))), LE(Int(0), x), LE(x, Int(1))
    )


def test_rewrite_splits_a_product_into_factor_congruences():
    p = _p()
    x, y = Symbol("x", INT), Symbol("y", INT)
    src = Equals(wrap_mod(Times(x, y)), Int(0))
    out = rewrite(src)

    assert out == Or(Equals(wrap_mod(x), Int(0)), Equals(wrap_mod(y), Int(0)))
    # ... and the split is truth-preserving on a small grid (cf. test_rewrite_choice).
    _agree_on(
        src,
        out,
        [{x: Int(i), y: Int(j)} for i in range(12) for j in range(12)],
    )


def test_rewrite_leaves_linear_congruences_to_normalize():
    """Division of labour, pinned deliberately.

    `(a - b) mod P = 0` is *not* rewrite's to solve -- `normalize` owns the modular
    form and `z3-solve-eqs` the elimination. If someone teaches `rewrite` to solve
    congruences again this fails, which is the intended signal: the passes would then
    both rewrite equalities and could disagree on the form (see the `rewrite` note in
    `simplifier.py` on why a later pass must not mangle rewrite's output).
    """
    _p()
    a, b = Symbol("a", INT), Symbol("b", INT)
    eq = Equals(wrap_mod(Plus(a, Times(Int(-1), b))), Int(0))
    assert rewrite(eq) == eq


def test_rewrite_leaves_a_non_product_linear_form_alone():
    """Likewise for constant folding: `normalize`'s job, not rewrite's."""
    _p()
    a, b, c = Symbol("a", INT), Symbol("b", INT), Symbol("c", INT)
    eq = Equals(
        wrap_mod(Plus(Int(512), Plus(Times(a, Int(0)), Times(b, Int(1)), Times(c, Int(2))), Int(-512))),
        Int(0),
    )
    assert rewrite(eq) == eq
