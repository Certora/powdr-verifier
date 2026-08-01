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
    # x=0 refuted, x=1 the sole survivor -> emitted as a forced-value pin.
    assert any(a == Equals(x, Int(1)) for a in asserts)


def test_domain_probe_pins_via_nonlinear_constraint():
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
    assert any(a == Equals(x, Int(1)) for a in asserts)


def test_domain_probe_strengthens_binary_disjunction():
    x = Symbol("x", INT)
    f = Or(Equals(x, Int(0)), Equals(x, Int(1)))
    smt = _script(f)
    with Action("domain_probe") as subaction:
        simplify_domain_probe(smt, subaction)
    asserts = [c.args[0] for c in smt if c.name == "assert"]
    assert len(asserts) == 1


def test_component_slice_keeps_flag_constraints_drops_wide_ones():
    """Components keep constraints over flag vars and drop wide columns."""
    from src.simplify.domain_probe import (
        _collect_choices,
        _component_slice,
        _const_pinned,
        _selector_components,
    )

    f = Symbol("opcode_and_flag", INT)  # small domain {0,1}
    a = Symbol("a__0_0", INT)  # wide, unbounded data column
    flag_dom = Or(Equals(f, Int(0)), Equals(f, Int(1)))
    wide = Equals(Times(f, a), a)  # mentions wide a -> not flag-local
    asserts = [flag_dom, wide]

    choices = _collect_choices(asserts, 3)
    pinned = _const_pinned(asserts)
    components = _selector_components(asserts, choices, pinned)

    assert components == [frozenset({f})]
    sliced = _component_slice(asserts, frozenset({f}), pinned)
    assert flag_dom in sliced
    assert wide not in sliced


def test_component_slice_links_pinned_aux_vars():
    from src.simplify.domain_probe import (
        _collect_choices,
        _component_slice,
        _const_pinned,
        _selector_components,
    )

    x = Symbol("x", INT)
    y = Symbol("y", INT)
    asserts = [
        And(
            Or(Equals(x, Int(0)), Equals(x, Int(1))),
            Equals(y, Int(0)),
        )
    ]
    choices = _collect_choices(asserts, 3)
    pinned = _const_pinned(asserts)
    components = _selector_components(asserts, choices, pinned)
    # y is a constant-pinned aux var, so the And is narrow and stays in the slice.
    assert components == [frozenset({x})]
    assert y in pinned
    sliced = _component_slice(asserts, frozenset({x}), pinned)
    assert asserts[0] in sliced


def test_domain_probe_adds_facts():
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    f = And(
        Or(Equals(x, Int(0)), Equals(x, Int(1))),
        Not(Equals(Plus(Times(x, x), Times(y, y)), Int(0))),
        Equals(y, Int(0)),
    )
    smt = _script(f)
    with Action("domain_probe") as subaction:
        out = simplify_domain_probe(smt, subaction)
    asserts = [c.args[0] for c in out if c.name == "assert"]
    # x=0 is refuted (x^2 != 0 with y=0), leaving x=1 forced: the confirmed
    # forced-value pin is emitted (exclusions are internal hints only).
    assert any(a == Equals(x, Int(1)) for a in asserts)
