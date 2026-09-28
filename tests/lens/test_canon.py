"""Factored canonical keys (src/lens/canon.py)."""
import pytest

from src.lens.canon import CanonError, canon_value, canon_zero, key_cols

P = 2013265921


def test_scalar_distributes_over_sum():
    # machine x - (y + 131072*w + 1)  vs  constraints x - y - 131072*w - 1
    m = ["x", "-", [["y", "+", [131072, "*", "w"]], "+", 1]]
    c = [[["x", "+", [P - 1, "*", "y"]], "+", [P - 131072, "*", "w"]], "+", P - 1]
    assert canon_value(m) == canon_value(c)


def test_scalar_moves_between_factors():
    a = [["f", "*", ["f", "-", 1]], "*", 1006632961]
    b = [[1006632961, "*", "f"], "*", ["f", "+", P - 1]]
    assert canon_value(a) == canon_value(b)


def test_products_are_not_expanded():
    assert canon_value(["x", "*", ["y", "+", "z"]]) != canon_value(
        [["x", "*", "y"], "+", ["x", "*", "z"]])


def test_product_is_associative_and_commutative():
    assert canon_value([["x", "*", "y"], "*", "z"]) == canon_value(
        ["z", "*", ["y", "*", "x"]])


def test_zero_key_ignores_units_value_key_does_not():
    assert canon_zero([P - 1, "*", "x"]) == canon_zero("x")
    assert canon_zero([6, "*", ["x", "+", 1]]) == canon_zero(["x", "+", 1])
    assert canon_value([P - 1, "*", "x"]) != canon_value("x")


def test_like_terms_and_nested_constants_merge():
    assert canon_value(["x", "-", "x"]) == ()
    assert canon_value([["x", "+", 3], "+", ["y", "+", 5]]) == canon_value(
        ["x", "+", ["y", "+", 8]])


def test_zero_factor_zeroes_product():
    assert canon_value(["x", "*", ["y", "-", "y"]]) == ()


def test_junk_raises():
    for bad in [True, None, {}, 1.5, [], ["x"], ["x", "/", "y"],
                ["x", "+", "y", "*", "z"], ["x", "*", None]]:
        with pytest.raises(CanonError):
            canon_value(bad)


def test_key_cols():
    cols: set = set()
    key_cols(canon_value([["a", "+", 1], "*", ["b", "-", "c"]]), cols)
    assert cols == {"a", "b", "c"}
