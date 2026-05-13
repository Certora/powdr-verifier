from src.simplify.skolem import SkolemMap
from src.simplify.skolem_rules import contribute
from src.smt.utils import *
from src.utils.args import parse_args


def _limb_disj(dm, b_sym, diff_val, cmp_sym, idx: int, p: int, extra_in_or: bool):
    sign = Plus(Int(p - 1), Times(Int(2), cmp_sym))
    if idx == 0:
        data_e = Plus(b_sym, Int(-1))
    else:
        data_e = b_sym
    inner = Plus(Times(data_e, sign), diff_val)
    mod_eq = Equals(Mod(inner, Int(p)), Int(0))
    dm_z = Equals(dm, Int(0))
    if extra_in_or:
        return Or(dm_z, mod_eq, Equals(Int(0), Int(0)))
    return Or(dm_z, mod_eq)


def test_equal_zero_check_or_flattened_still_pins_diff_val():
    parse_args(["simplify", "/tmp/x", "nnf", "/tmp/y"])
    p = ARGS().field_type.value
    dv = Symbol("before-diff_val_0@1", INT)
    dm0 = Symbol("before-diff_marker__0_0@10", INT)
    dm1 = Symbol("before-diff_marker__1_0@11", INT)
    dm2 = Symbol("before-diff_marker__2_0@12", INT)
    dm3 = Symbol("before-diff_marker__3_0@13", INT)
    b0 = Symbol("before-a__0_0@20", INT)
    b1 = Symbol("before-a__1_0@21", INT)
    b2 = Symbol("before-a__2_0@22", INT)
    b3 = Symbol("before-a__3_0@23", INT)
    cmp_b = Symbol("before-cmp_result_0@30", INT)

    limbs = [
        _limb_disj(dm0, b0, dv, cmp_b, 0, p, extra_in_or=True),
        _limb_disj(dm1, b1, dv, cmp_b, 1, p, extra_in_or=True),
        _limb_disj(dm2, b2, dv, cmp_b, 2, p, extra_in_or=False),
        _limb_disj(dm3, b3, dv, cmp_b, 3, p, extra_in_or=True),
    ]
    body = And(*limbs)
    forall = ForAll([dv, dm0, dm1, dm2, dm3], Or(Not(Equals(b0, b1)), body))

    m = SkolemMap([dv, dm0, dm1, dm2, dm3])
    contribute(m, forall.arg(0))
    assert m.is_pinned(dv), "diff_val should pin with n-ary Or DiffMarker shapes"
    assert m.is_pinned(dm0) and m.is_pinned(dm1)


def test_named_openvm_limbs_pins_without_diff_marker_products():
    parse_args(["simplify", "/tmp/x", "nnf", "/tmp/y"])
    g = 2
    row = 2 * (g - 1)
    dv = Symbol("before-diff_val_2@109", INT)
    cmp_v = Symbol("before-cmp_result_2@100", INT)
    dms = [Symbol(f"before-diff_marker__{i}_{g}@{105 + i}", INT) for i in range(4)]
    bs = [Symbol(f"before-b__{i}_{row}@{92 + i}", INT) for i in range(4)]
    syms = [dv, cmp_v, *dms, *bs]
    body = Equals(Plus(*syms), Plus(*syms))
    forall = ForAll([dv, *dms], Or(Equals(Int(1), Int(0)), body))
    m = SkolemMap([dv, *dms])
    contribute(m, forall.arg(0))
    assert m.is_pinned(dv)
    assert m.is_pinned(dms[0])
