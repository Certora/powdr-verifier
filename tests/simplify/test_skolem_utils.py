from src.simplify.skolem_utils import emit_pin_setinfo, load_skolem_setinfos, split_equation
from src.smt.utils import *
from src.verify import SetInfos, SkolemPinKind, skolem_setinfo_keyword_prefix

from pysmt.smtlib import script


def test_split_equation_equals():
    x, y = Symbol("sx", INT), Symbol("sy", INT)
    assert split_equation(Equals(x, y)) == (x, y)
    assert split_equation(Equals(Int(1), x)) == (x, Int(1))


def test_split_equation_iff_bool():
    a, b = Symbol("sa", BOOL), Symbol("sb", BOOL)
    assert split_equation(Iff(a, b)) == (a, b)
    assert split_equation(Iff(FALSE(), a)) == (a, FALSE())


def test_split_equation_iff_no_symbol_side():
    assert split_equation(Iff(TRUE(), TRUE())) is None


def test_split_equation_rejects_non_pin_shape():
    assert split_equation(Or(TRUE(), FALSE())) is None


def test_load_skolem_setinfos_preserves_script_order_and_kinds():
    x = Symbol("px", INT)
    eq = Equals(x, Int(3))
    smt = script.SmtLibScript()
    smt.commands = [
        script.SmtLibCommand("declare-fun", [x]),
        emit_pin_setinfo(skolem_setinfo_keyword_prefix(SkolemPinKind.SUBSTITUTION), 0, eq),
        emit_pin_setinfo(skolem_setinfo_keyword_prefix(SkolemPinKind.DERIVED), 0, eq),
    ]
    out = load_skolem_setinfos(smt)
    assert isinstance(out, SetInfos)
    assert len(out.equations) == 2
    assert out.equations[0].pin_type == SkolemPinKind.SUBSTITUTION
    assert out.equations[1].pin_type == SkolemPinKind.DERIVED
    assert out.equations[0].node.to_smtlib(daggify=False) == eq.to_smtlib(daggify=False)
    assert out.equations[1].node.to_smtlib(daggify=False) == eq.to_smtlib(daggify=False)
