"""Regression: resource-exhaustion outcomes must not be classified as ``error``.

When z3 cannot finish an ``unsat``-expected obligation under the benchmark's
per-job memory/time budget it returns ``unknown`` with a ``:reason-unknown`` of
``"out of memory"`` (address-space cap hit) or ``"canceled"`` (wall-clock
``timeout`` fired outside the main search loop). These are resource limits, not
hard errors -- and the leaf ``check-attempt`` node (which carries no
``expected``) already buckets the very same strings as ``memout``. The parent
``solve``/``check`` node (which does carry ``expected``) must agree.
"""
from src.report.action import (
    Action,
    classify_expected_vs_result,
    is_memout_reason,
    is_timeout_reason,
)


def test_out_of_memory_is_memout_not_error():
    # 6 of the 9 guest-keccak benchmark "errors" (blocks 2099828 / 2102932).
    assert (
        classify_expected_vs_result(
            name="solve", expected="unsat", result="unknown-out of memory"
        )
        == "memout"
    )


def test_canceled_is_timeout_not_error():
    # 3 of the 9 guest-keccak benchmark "errors" (2104024 / 2105016 / 2106356):
    # z3's timeout fired but reported "canceled" instead of "timeout".
    assert (
        classify_expected_vs_result(
            name="solve", expected="unsat", result="unknown-canceled"
        )
        == "timeout"
    )


def test_leaf_and_parent_agree_on_reason():
    """The leaf (no ``expected``) and parent (``expected``) must not disagree."""
    for result, bucket in [
        ("unknown-out of memory", "memout"),
        ("unknown-canceled", "timeout"),
    ]:
        parent = classify_expected_vs_result(
            name="solve", expected="unsat", result=result
        )
        leaf = Action("check-attempt", result=result).status()
        assert parent == bucket
        assert leaf == bucket, (result, leaf, parent)


def test_genuine_unknown_still_error():
    # A bare "unknown" with no resource reason stays an error (unchanged).
    assert (
        classify_expected_vs_result(name="solve", expected="unsat", result="unknown")
        == "error"
    )


def test_reason_predicates():
    assert is_memout_reason("out of memory")
    assert is_memout_reason("std::bad_alloc")
    assert not is_memout_reason("canceled")
    assert not is_memout_reason("")
    assert is_timeout_reason("canceled")
    assert is_timeout_reason("cancelled")
    assert is_timeout_reason("timeout")
    assert is_timeout_reason("resource limits reached")
    assert not is_timeout_reason("out of memory")


def test_aggregated_step_status():
    """A full verify step: completeness unsat + soundness canceled -> timeout,
    not error (matches the 2104024/2105016/2106356 shape)."""
    check_ok = Action("check", expected="unsat", result="unsat")
    check_bad = Action("check", expected="unsat", result="unknown-canceled")
    verify = Action("verify")
    verify.actions = [check_ok, check_bad]
    assert verify.status() == "timeout"

    # Both sides OOM -> memout (the 2099828/2102932 shape).
    verify2 = Action("verify")
    verify2.actions = [
        Action("check", expected="unsat", result="unknown-out of memory"),
        Action("check", expected="unsat", result="unknown-out of memory"),
    ]
    assert verify2.status() == "memout"
