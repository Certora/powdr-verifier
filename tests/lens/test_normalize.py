"""Signed-constant normalization (toward negative, BabyBear p)."""
from src.lens.normalize import BABYBEAR_PRIME, normalize_constants, to_signed


def test_to_signed():
    assert to_signed(2013265920) == -1      # p-1 -> -1
    assert to_signed(1) == 1
    assert to_signed(BABYBEAR_PRIME) == 0    # p -> 0
    assert to_signed(0) == 0
    assert to_signed(BABYBEAR_PRIME - 5) == -5


def test_normalize_constants_folds_unary_minus():
    assert normalize_constants(["-", 1]) == -1
    assert normalize_constants(["-", ["-", 1]]) == 1


def test_normalize_constants_signs_residue_in_tree():
    expr = [[2013265920, "*", "cmp@95"], "+", 1]
    assert normalize_constants(expr) == [[-1, "*", "cmp@95"], "+", 1]


def test_normalize_constants_keeps_columns_and_unary_over_expr():
    assert normalize_constants("x@0") == "x@0"
    assert normalize_constants(["-", ["a@0", "+", "b@1"]]) == ["-", ["a@0", "+", "b@1"]]
