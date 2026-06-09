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


def test_quantified_contribute_does_not_pin_without_diff_marker_products():
    """The quantified ``contribute`` path no longer name-fabricates a witness.

    When the ``DiffMarkerConstraint`` products are absent (powdr reduced the
    LessThan gadget to a free, range-checked ``diff_val`` cluster), the
    name-only fallback would pin a witness (``(c[i]-b[i])*sign``) that ignores
    the surviving range check and yields a spurious soundness sat
    (guest-keccak 2104744 014->015). ``contribute`` disables that fallback
    (``allow_name_fallback=False``) so the closed-island ``skolem_isolate``
    pass can supply a range-satisfying witness instead. ``contribute_free``
    keeps the fallback (its quantified counterpart still carries the gadget).
    See journal 2026-06-09.
    """
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
    assert not m.is_pinned(dv), "name-only fallback must be disabled in contribute"
    assert not any(m.is_pinned(dm) for dm in dms)


def test_named_openvm_limbs_still_pin_in_contribute_free():
    """``contribute_free`` retains the name fallback for free diff_val columns.

    A *free* (non-quantified) ``after-diff_val`` whose quantified ``before-``
    counterpart still carries the gadget is witnessed by reconstructing from
    the before side and swapping prefixes. The name fallback is reached on the
    quantified side; this guards that the legitimate reconstruction survives
    the ``contribute`` workaround.
    """
    parse_args(["simplify", "/tmp/x", "nnf", "/tmp/y"])
    p = ARGS().field_type.value
    # before-side (quantified) carries the real DiffMarkerConstraint products.
    dv_b = Symbol("before-diff_val_0@1", INT)
    dms_b = [Symbol(f"before-diff_marker__{i}_0@{10 + i}", INT) for i in range(4)]
    bs_b = [Symbol(f"before-a__{i}_0@{20 + i}", INT) for i in range(4)]
    cmp_b = Symbol("before-cmp_result_0@30", INT)
    # after-side (free) counterpart that contribute_free should witness.
    dv_a = Symbol("after-diff_val_0@1", INT)
    dms_a = [Symbol(f"after-diff_marker__{i}_0@{10 + i}", INT) for i in range(4)]
    bs_a = [Symbol(f"after-a__{i}_0@{20 + i}", INT) for i in range(4)]
    cmp_a = Symbol("after-cmp_result_0@30", INT)

    limbs = [
        _limb_disj(dms_b[i], bs_b[i], dv_b, cmp_b, i, p, extra_in_or=False)
        for i in range(4)
    ]
    body = Or(Not(Equals(bs_b[0], bs_b[1])), And(*limbs))
    forall = ForAll([dv_b, *dms_b], body)

    smt_script = script.SmtLibScript()
    decls = [dv_b, *dms_b, *bs_b, cmp_b, dv_a, *dms_a, *bs_a, cmp_a]
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [s, [], s.get_type()]) for s in decls
    ] + [script.SmtLibCommand("assert", [forall])]

    from src.simplify.skolem_rules import contribute_free
    pins = contribute_free(smt_script, {dv_b, *dms_b})
    pinned_vars = {var for var, _ in pins}
    assert dv_a in pinned_vars, "contribute_free should still witness the free after-diff_val"
