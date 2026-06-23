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


def test_flag_cluster_slice_keeps_flag_constraints_drops_wide_ones():
    """Per-seed clusters keep constraints over flag vars and drop wide columns."""
    from src.simplify.domain_probe import (
        _cluster_assertions,
        _collect_choices,
        _flag_cluster,
    )

    f = Symbol("opcode_and_flag", INT)  # small domain {0,1}
    a = Symbol("a__0_0", INT)  # wide, unbounded data column
    flag_dom = Or(Equals(f, Int(0)), Equals(f, Int(1)))
    wide = Equals(Times(f, a), a)  # mentions wide a -> not flag-local
    asserts = [flag_dom, wide]

    choices = _collect_choices(asserts, 3)
    cluster = _flag_cluster(f, asserts, choices)

    assert f in cluster
    assert a not in cluster
    sliced = _cluster_assertions(asserts, cluster)
    assert flag_dom in sliced
    assert wide not in sliced


def test_flag_cluster_links_pinned_aux_vars():
    from src.simplify.domain_probe import _collect_choices, _flag_cluster

    x = Symbol("x", INT)
    y = Symbol("y", INT)
    asserts = [
        And(
            Or(Equals(x, Int(0)), Equals(x, Int(1))),
            Equals(y, Int(0)),
        )
    ]
    choices = _collect_choices(asserts, 3)
    cluster = _flag_cluster(x, asserts, choices)
    assert cluster == frozenset({x, y})


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
