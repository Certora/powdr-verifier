from src.rewriter.rewrites import rewrite_choice_simple
from src.smt.utils import *
from src.utils.args import parse_args


def test_rewrite_choice_simple_equivalent_mod_zero():
    parse_args(["check", "x"])
    p = ARGS().field_type.value

    for a_val in range(min(p, 32)):
        for b_val in range(min(p, 32)):
            a = Int(a_val)
            b = Int(b_val)
            prod_zero = Equals(Mod(Times(a, b), Int(p)), Int(0))
            split_zero = rewrite_choice_simple(
                operators.EQUALS, [Mod(Times(a, b), Int(p)), Int(0)]
            )
            assert split_zero is not None
            if prod_zero.is_true() != split_zero.is_true():
                raise AssertionError((a_val, b_val, prod_zero, split_zero))
