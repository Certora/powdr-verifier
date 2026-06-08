from src.simplify.lift_forall import simplify_lift_forall
from src.smt.utils import *


def _script_assert(f):
    s = script.SmtLibScript()
    s.commands = [script.SmtLibCommand("assert", [f])]
    return s


def _top_asserts(script):
    return [cmd.args[0] for cmd in script.commands if cmd.name == "assert"]


def test_lift_single_var_drops_forall_keeps_body():
    x = Symbol("lx", INT)
    inner = Or(Not(Equals(x, Int(7))), LT(x, Int(0)))
    f = ForAll([x], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[-1].args[0]
    assert out == LT(x, Int(0))
    assert Equals(x, Int(7)) in _top_asserts(simplify_lift_forall(_script_assert(f)))
    assert not out.is_forall()


def test_lift_two_vars_in_sequence():
    x, y = Symbol("lx2", INT), Symbol("ly2", INT)
    inner = Or(Not(Equals(x, Int(1))), Not(Equals(y, Int(2))), LT(y, x))
    f = ForAll([x, y], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[-1].args[0]
    assert out == LT(y, x)
    assert not out.is_forall()


def test_skips_when_expr_mentions_other_quantified_int():
    x, y = Symbol("lsx", INT), Symbol("lsy", INT)
    inner = Or(Not(Equals(x, y)), LT(x, Int(0)))
    f = ForAll([x, y], inner)
    out = simplify_lift_forall(_script_assert(f)).commands[-1].args[0]
    assert out == f
    assert out.is_forall() and list(out.quantifier_vars()) == list(f.quantifier_vars())


def test_lift_int_defined_from_array_select():
    a = Symbol("lift_mem_a", ArrayType(INT, INT))
    v = Symbol("lift_mem_a-1", INT)
    key = Int(3)
    inner = Or(Not(Equals(v, Select(a, key))), LT(v, Int(0)))
    f = ForAll([a, v], inner)
    script = simplify_lift_forall(_script_assert(f))
    out = script.commands[-1].args[0]
    assert out.is_forall()
    assert list(out.quantifier_vars()) == [a]
    assert out.arg(0) == LT(v, Int(0))
    assert Equals(v, Select(a, key)) in _top_asserts(script)


def test_lift_int_chain_defined_from_array_selects():
    base = Symbol("lift_base", ArrayType(INT, ArrayType(INT, INT)))
    mid = Symbol("lift_base-mid", ArrayType(INT, INT))
    v2 = Symbol("lift_base-2", INT)
    inner = Or(
        Not(Equals(mid, Select(base, Int(1)))),
        Not(Equals(v2, Select(mid, Int(2)))),
        LT(v2, Int(0)),
    )
    f = ForAll([base, mid, v2], inner)
    script = simplify_lift_forall(_script_assert(f))
    out = script.commands[-1].args[0]
    assert out.is_forall()
    assert list(out.quantifier_vars()) == [base]
    assert out.arg(0) == LT(v2, Int(0))
    top = _top_asserts(script)
    assert Equals(v2, Select(mid, Int(2))) in top
    assert Equals(mid, Select(base, Int(1))) in top


def test_lift_array_defined_from_select():
    base = Symbol("lift_arr_base", ArrayType(INT, ArrayType(INT, INT)))
    mid = Symbol("lift_arr_mid", ArrayType(INT, INT))
    inner = Or(Not(Equals(mid, Select(base, Int(1)))), TRUE())
    f = ForAll([base, mid], inner)
    script = simplify_lift_forall(_script_assert(f))
    out = script.commands[-1].args[0]
    assert out.is_forall()
    assert list(out.quantifier_vars()) == [base]
    assert Equals(mid, Select(base, Int(1))) in _top_asserts(script)


def test_removes_lifted_disjunct_from_or():
    x = Symbol("lift_x", INT)
    inner = Or(Not(Equals(x, Int(0))), x > Int(1))
    f = ForAll([x], inner)
    script = simplify_lift_forall(_script_assert(f))
    out = script.commands[-1].args[0]
    assert out == (x > Int(1))
    assert Equals(x, Int(0)) in _top_asserts(script)


def test_lift_bool_iff_hoists():
    p = Symbol("lift_iff_p", BOOL)
    inner = Or(Not(Iff(p, TRUE())), FALSE())
    f = ForAll([p], inner)
    script = simplify_lift_forall(_script_assert(f))
    out = script.commands[-1].args[0]
    assert out == FALSE()
    assert Iff(p, TRUE()) in _top_asserts(script)
