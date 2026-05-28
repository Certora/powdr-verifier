from src.simplify.lift_forall import simplify_lift_forall
from src.simplify.skolem import simplify_skolem
from src.smt.utils import *


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def test_isolate_skolem_adds_liftable_model_for_local_quantified_var():
    x = Symbol("isolated_x", INT)
    y = Symbol("external_y", INT)
    body = Or(LE(x, Int(0)), LE(Int(10), x), LT(y, Int(0)))
    smt_script = _script(ForAll([x], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    out = lifted.commands[-1].args[0]

    assert not out.is_forall()
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == x
    ]
    assert pins


def test_isolate_skolem_extracts_from_and_disjunct_with_other_free_vars():
    x = Symbol("isolated_x2", INT)
    y = Symbol("external_y2", INT)
    body = Or(And(LE(x, Int(0)), LE(Int(10), x)), LT(y, Int(0)))
    smt_script = _script(ForAll([x], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == x
    ]
    assert pins


def test_isolate_does_not_pin_with_outer_free_var():
    """Regression: a q-mentioning disjunct that *also* mentions an outer
    (non-qvar) free variable must disqualify the qvar from isolation.

    The probe inside ``_find_isolated_value`` only sees one outer-variable
    assignment chosen by the solver; the witness it returns is valid for
    that assignment, but the underlying existential ``∃q. ¬⋁_i D_i(q, x)``
    in the definition of "F unsat" has a "bad q" that depends on ``x``. A
    pin from this probe is therefore unsound for unsat-proving (turns
    F-unsat into F'-sat). Verified empirically on
    ``apc_candidate_2099512_031_low_degree_bus-…_032_inlining.completeness``
    where the buggy version pinned ``after-memory-N-isinput := False`` even
    though the formula entailed ``isinput = True``.

    The disjunct ``q = y`` mentions qvar ``q`` and outer free var ``y``.
    Without the soundness gate the probe would pick a model with some
    ``y = y*`` and pin ``q := y*``, over-constraining ``y`` for the rest
    of the formula.
    """
    q = Symbol("isolated_q_with_outer", INT)
    y = Symbol("outer_y_in_disjunct", INT)
    # body: (q = y) ∨ (q = 7)
    # Both disjuncts mention q; the first ALSO mentions outer y.
    # The probe might find e.g. (q=0, y=1) sat (negates both disjuncts) and
    # pin q := 0 — but in the actual model y could equal 0, in which case
    # the original disjunction q=y holds and q can be ANY value.
    body = Or(Equals(q, y), Equals(q, Int(7)))
    smt_script = _script(ForAll([q], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == q
    ]
    assert not pins, f"isolate should NOT pin q here; got pins: {pins}"


def test_isolate_does_not_pin_with_other_qvar_in_disjunct():
    """A disjunct mentioning multiple qvars also disqualifies isolation.

    The pin would establish the body at one specific assignment of the
    "other" qvar (the model the probe happens to find), but the rest of
    the formula could force a different value on that other qvar.

    Verified empirically: an earlier "other qvars in same disjunct are
    fine" relaxation pinned ``after-memory-N-isinput := False`` on the
    keccak benchmarks because a disjunct ``(= isinput (not hadinput-2))``
    mentions both qvars and the probe's model picked ``hadinput-2 = True``
    — but the rest of the formula entailed ``hadinput-2 = False``.
    """
    a = Symbol("multi_q_a", INT)
    b = Symbol("multi_q_b", INT)
    body = Or(Equals(a, b), Equals(a, Int(7)))
    smt_script = _script(ForAll([a, b], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals()
        and c.args[0].arg(0) in (a, b)
    ]
    assert not pins, f"isolate should not pin multi-qvar disjuncts; got: {pins}"
