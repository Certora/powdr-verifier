from src.simplify.domain_probe import simplify_domain_probe
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_domain_probe_skips_singleton_interval_domain():
    x = Symbol("x", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        LE(Int(1), x),
        LE(x, Int(1)),
    )
    smt = _script(f)
    simplify_domain_probe(smt)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert len(asserts) == 1


def test_domain_probe_excludes_via_nonlinear_constraint():
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        Not(Equals(Plus(Times(x, x), Times(y, y)), Int(0))),
        Equals(y, Int(0)),
    )
    smt = _script(f)
    simplify_domain_probe(smt)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert any(a == Not(Equals(x, Int(0))) for a in asserts)


def test_domain_probe_strengthens_binary_disjunction():
    x = Symbol("x", INT)
    f = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    smt = _script(f)
    simplify_domain_probe(smt)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert len(asserts) == 3
    assert Equals(x, Int(0)) in asserts
    assert Not(Equals(x, Int(1))) in asserts
