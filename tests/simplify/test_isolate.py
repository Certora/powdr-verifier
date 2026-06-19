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


def test_isolate_pins_qvar_in_and_disjunct_with_outer_sibling_conjunct():
    """The powdr ``remove_free`` shape: ``(P(x) ∧ Q(outer))``.

    The qvar ``x`` lives only in conjunct ``P(x)`` of an ``And``-disjunct whose
    sibling conjunct ``Q(y)`` mentions only the outer var ``y``. ``x`` and ``y``
    never share an *atom* — only the ``And`` — so ``x`` is a closed sub-island
    and must be pinned. Forall distributes:
    ``∀x.(E ∨ (P(x) ∧ Q(y))) = E ∨ (Q(y) ∧ ∀x.P(x))`` — the witness search only
    touches ``P``, and ``Q`` is dropped from the probe. Mirrors
    ``before-diff_val_2@108`` on ``2106368`` 015→016 (journal 2026-06-18).
    """
    x = Symbol("free_x_in_and", INT)
    y = Symbol("outer_y_sibling", INT)
    # P(x): NOT(x <= 0)  (i.e. x > 0), falsifiable at x = 0
    # Q(y): NOT(y <= 0)  — outer only
    body = Or(
        And(Not(LE(x, Int(0))), Not(LE(y, Int(0)))),
        LT(y, Int(3)),
    )
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
    assert pins, "x should be pinned: its conjunct P(x) is outer-independent"
    # the outer sibling var must NOT be pinned
    ypins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == y
    ]
    assert not ypins, f"outer var y must not be pinned; got: {ypins}"


def test_isolate_does_not_pin_qvar_coupled_inside_and_disjunct():
    """Per-conjunct taint still rejects a qvar that shares an *atom* with an
    outer var, even when that atom sits inside an ``And``-disjunct.

    Here conjunct ``q = y`` mixes qvar ``q`` and outer ``y`` in one atom, so
    ``R`` mentions ``y`` ∉ island ⇒ tainted. (Contrast the test above, where
    the qvar and the outer var are in *separate* conjuncts.)
    """
    q = Symbol("coupled_q_in_and", INT)
    y = Symbol("outer_y_in_and_atom", INT)
    body = Or(
        And(Equals(q, y), Not(LE(q, Int(0)))),
        LT(y, Int(3)),
    )
    smt_script = _script(ForAll([q], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals() and c.args[0].arg(0) == q
    ]
    assert not pins, f"q shares an atom with outer y; must not be pinned; got: {pins}"


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


def test_isolate_pins_closed_multi_qvar_island():
    """A multi-qvar disjunct is fine when the whole component is *closed*.

    ``{a, b}`` form a closed island: every disjunct mentioning either of them
    mentions only ``a``/``b`` (no outer free var, no other qvar). The island is
    decoupled from the rest of the formula, so any satisfying assignment is a
    uniform witness and both are pinned jointly from one model. This is the
    ``diff_marker__*`` / ``diff_val_*`` cluster shape left by powdr
    ``remove_free`` (see journal 2026-06-09).
    """
    a = Symbol("island_q_a", INT)
    b = Symbol("island_q_b", INT)
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
    assert {p.arg(0) for p in pins} == {a, b}, f"expected both a and b pinned; got: {pins}"


def test_isolate_does_not_pin_qvar_island_coupled_to_outer():
    """A multi-qvar component reaching an outer free var is NOT pinned.

    ``a`` and ``b`` co-occur (``a = b``), and ``b`` *also* shares a disjunct
    with the outer free var ``y`` (``b = y``). The component ``{a, b}`` is
    therefore tainted: a one-shot probe model fixes ``y`` to one value and the
    pin would only be valid for that value, while the rest of the formula can
    force a different ``y``. This is the failure mode the old strict gate
    guarded against (``after-memory-N-isinput`` / ``hadinput`` on the keccak
    benchmarks), preserved transitively.
    """
    a = Symbol("coupled_q_a", INT)
    b = Symbol("coupled_q_b", INT)
    y = Symbol("coupled_outer_y", INT)
    body = Or(Equals(a, b), Equals(b, y), Equals(a, Int(7)))
    smt_script = _script(ForAll([a, b], body))

    skolem = simplify_skolem(smt_script)
    lifted = simplify_lift_forall(skolem)
    pins = [
        c.args[0]
        for c in lifted.commands
        if c.name == "assert" and c.args[0].is_equals()
        and c.args[0].arg(0) in (a, b)
    ]
    assert not pins, f"tainted component must not be pinned; got: {pins}"
