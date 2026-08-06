"""Tests for granting before-side memory byte facts as soundness premises.

Two halves:

* the ``--soundness-before-consequences`` selector, which is pure bookkeeping over
  ``ConsequenceKind``;
* the *property* the grant is supposed to have, checked on a hand-built model of the
  situation rather than on a real block. The real-block version of this needs a
  60s-capped solver run per arm; the mechanism is small enough to model in a handful
  of asserts, so it runs in milliseconds and can gate every commit.

``test_corrupted_read_sourced_write_is_masked`` deliberately asserts the *limitation*:
the grant does mask a non-byte write on a read-sourced column. That is the accepted
risk of the change, and it is pinned here so it stays a known, tested scope rather
than a surprise.
"""
from src.smt.conversion import FormulaWithAxioms
from src.smt.utils import *
from src.utils.args import ARGS, parse_args
from src.verifier import _soundness_before_premises


def _args(*modes: str) -> None:
    extra = ["--soundness-before-consequences", ",".join(modes)] if modes else []
    parse_args([*extra, "check", "x"])


def _formula(consequences) -> FormulaWithAxioms:
    return FormulaWithAxioms(
        constraints=[], consequences=list(consequences), axioms=[], derived={}, globals=frozenset()
    )


def _sym(name: str) -> FNode:
    return Symbol(name, INT)


def _byte(v: FNode) -> FNode:
    return And(LE(Int(0), v), LE(v, Int(255)))


# --------------------------------------------------------------------------- #
# selector
# --------------------------------------------------------------------------- #

BYTES_F, TS_F, RANGE_F, BARE_F = (_sym("b"), _sym("t"), _sym("r"), _sym("u"))


def _mixed():
    return _formula(
        [
            Consequence(ConsequenceKind.MEMORY_RECV_BYTES, BYTES_F),
            Consequence(ConsequenceKind.MEMORY_TIMESTAMP_BOUNDS, TS_F),
            Consequence(ConsequenceKind.RANGE_INFERENCE, RANGE_F),
            BARE_F,  # untagged producers stay supported
        ]
    )


def test_default_grants_only_the_memory_byte_facts():
    _args()  # no flag -> the default
    assert ARGS().soundness_before_consequences == ["bytes"]
    assert _soundness_before_premises(_mixed()) == [BYTES_F]


def test_none_grants_nothing():
    _args("none")
    assert _soundness_before_premises(_mixed()) == []


def test_none_overrides_any_other_kind():
    _args("bytes", "none")
    assert _soundness_before_premises(_mixed()) == []


def test_kinds_are_unioned():
    _args("bytes", "timestamps")
    assert _soundness_before_premises(_mixed()) == [BYTES_F, TS_F]


def test_all_grants_every_consequence_including_untagged():
    _args("all")
    assert _soundness_before_premises(_mixed()) == [BYTES_F, TS_F, RANGE_F, BARE_F]


def test_untagged_is_selectable_but_not_part_of_bytes():
    _args("untagged")
    assert _soundness_before_premises(_mixed()) == [BARE_F]


def test_constant_guards_are_decided():
    """A grant is `mult = -1 mod P -> data are bytes` per row with the guard left
    unevaluated (`demod` runs after `lift`). Selecting it simplifies: a live recv keeps
    the bare range, a disabled `mult = 0` row folds to true and drops out."""
    _args()
    d = _sym("d")

    def grant(mult: int) -> Consequence:
        guard = Equals(wrap_mod(Plus(Int(mult), Int(1))), Int(0))
        return Consequence(ConsequenceKind.MEMORY_RECV_BYTES, Implies(guard, _byte(d)))

    # (simplify is set-based over `And`, so compare against the simplified range)
    assert _soundness_before_premises(_formula([grant(-1)])) == [_byte(d).simplify()]
    assert _soundness_before_premises(_formula([grant(0)])) == []
    # ... and a symbolic multiplicity is undecidable here, so it keeps its guard.
    m = _sym("m")
    sym = Implies(Equals(wrap_mod(Plus(m, Int(1))), Int(0)), _byte(d))
    assert _soundness_before_premises(
        _formula([Consequence(ConsequenceKind.MEMORY_RECV_BYTES, sym)])
    ) == [sym]


# --------------------------------------------------------------------------- #
# the property
#
# Post-`lift` shape of the soundness VC, which is what the checker actually sees:
# the before columns are free and pinned to their after counterparts, so the whole
# artifact is quantifier-free. `unsat` == the obligation is discharged (a PASS).
#
#   premises : the after circuit's constraints, plus the transported grant
#   pin      : before-X = after-X  (hoisted out of the ForAll by `lift`)
#   goal     : the before circuit's send byte obligation, negated
# --------------------------------------------------------------------------- #

B_D, A_D = _sym("before-d"), _sym("after-d")  # a read-sourced data column
B_W, A_W = _sym("before-w"), _sym("after-w")  # written, never read


def _vc(after_constraints, granted, obligation) -> FNode:
    """`unsat` iff the obligation is discharged."""
    pins = [Equals(B_D, A_D), Equals(B_W, A_W)]
    return And(*after_constraints, *granted, *pins, Not(obligation))


def test_without_the_grant_the_obligation_is_not_provable():
    """The bug being fixed: the `memory` pass deleted the recv, so nothing on the
    after side bounds the column, and the before side's write obligation cannot be
    discharged."""
    assert is_sat(_vc(after_constraints=[], granted=[], obligation=_byte(B_D)))


def test_the_grant_discharges_the_obligation():
    assert is_unsat(_vc(after_constraints=[], granted=[_byte(B_D)], obligation=_byte(B_D)))


def test_grant_does_not_mask_a_non_byte_write_on_an_ungranted_column():
    """The safety property. `w` is written but never read, so it gets no grant; a
    circuit that writes 256 into it must still be caught."""
    vc = _vc(
        after_constraints=[Equals(A_W, Int(256))],
        granted=[_byte(B_D)],  # granted for d only
        obligation=_byte(B_W),
    )
    assert is_sat(vc), "a non-byte write on an ungranted column must still be caught"


def test_corrupted_read_sourced_write_is_masked():
    """The accepted limitation, pinned deliberately.

    On a read-sourced column the grant and the obligation are the same predicate, so
    a circuit that writes 256 there makes the premises contradictory and the artifact
    comes back `unsat` -- a vacuous PASS. Granting bytes for such a column means no
    longer checking that the circuit writes bytes into it.

    If this test ever starts failing, the grant has been narrowed (e.g. to exclude
    columns that are also send data) and the risk note on
    ``_soundness_before_premises`` can be relaxed.
    """
    vc = _vc(
        after_constraints=[Equals(A_D, Int(256))],
        granted=[_byte(B_D)],
        obligation=_byte(B_D),
    )
    assert is_unsat(vc), "documents the masking; see the docstring"
    # ... and without the grant the same corruption is caught, which is what makes
    # this a masking result rather than an inherently undetectable bug.
    assert is_sat(
        _vc(after_constraints=[Equals(A_D, Int(256))], granted=[], obligation=_byte(B_D))
    )
