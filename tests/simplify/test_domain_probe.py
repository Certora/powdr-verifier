from src.report.action import Action
from src.simplify.domain_probe import simplify_domain_probe
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_domain_probe_excludes_singleton_via_bounds():
    x = Symbol("x", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        LE(Int(1), x),
        LE(x, Int(1)),
    )
    smt = _script(f)
    with Action("domain_probe") as subaction:
        simplify_domain_probe(smt, subaction)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert any(a == Not(Equals(x, Int(0))) for a in asserts)


def test_domain_probe_excludes_via_nonlinear_constraint():
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        Not(Equals(Plus(Times(x, x), Times(y, y)), Int(0))),
        Equals(y, Int(0)),
    )
    smt = _script(f)
    with Action("domain_probe") as subaction:
        simplify_domain_probe(smt, subaction)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert any(a == Not(Equals(x, Int(0))) for a in asserts)


def test_domain_probe_strengthens_binary_disjunction():
    x = Symbol("x", INT)
    f = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    smt = _script(f)
    with Action("domain_probe") as subaction:
        simplify_domain_probe(smt, subaction)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert len(asserts) == 1


def test_flag_local_slice_keeps_flag_constraints_drops_wide_ones():
    """Flag-local slicing keeps constraints over small-domain (flag) vars and
    drops those touching wide data columns, so a flag probe doesn't drag the
    nonlinear bus arithmetic into the solver (the 202s->3.5s win on 2105476)."""
    from src.simplify.domain_probe import (
        _collect_choices,
        _flag_local_assertions,
        _small_domain_vars,
    )

    f = Symbol("opcode_and_flag", INT)  # small domain {0,1}
    a = Symbol("a__0_0", INT)  # wide, unbounded data column
    flag_dom = Or(Equals(f, Int(0)), Equals(f, Int(1)))
    wide = Equals(Times(f, a), a)  # mentions wide a -> not flag-local
    asserts = [flag_dom, wide]

    choices = _collect_choices(asserts, 3)
    flags = _small_domain_vars(asserts, choices, 3)

    assert f in flags  # {0,1} -> flag-like
    assert a not in flags  # unbounded -> not flag-like
    sliced = _flag_local_assertions(asserts, flags)
    assert flag_dom in sliced  # flag-only constraint kept
    assert wide not in sliced  # data-touching constraint dropped


def test_domain_probe_subaction_added_facts():
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        Not(Equals(Plus(Times(x, x), Times(y, y)), Int(0))),
        Equals(y, Int(0)),
    )
    smt = _script(f)
    with Action("domain_probe") as subaction:
        simplify_domain_probe(smt, subaction)
    assert subaction.added_facts == 1
