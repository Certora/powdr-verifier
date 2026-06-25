"""Constraint-level diff: canonicalization, classification, rendering."""
import json

import pytest

from src.lens.diff import DiffError, build_diff, canon_constraint
from src.lens.render import JSON, PLAIN, Target, render_diff


def _c(constraints):
    """A constraints-format (grouped) dump: no '-' operator."""
    return {"constraints": constraints, "bus_interactions": [],
            "derived_columns": []}


def _m(constraints):
    """A machine-format dump: uses the '-' operator."""
    return {"constraints": constraints, "bus_interactions": [],
            "derived_columns": []}


# --- canonicalization -------------------------------------------------------
def test_canon_commutative_and_assoc():
    assert canon_constraint(["a@0", "+", "b@1"]) == canon_constraint(["b@1", "+", "a@0"])
    assert (canon_constraint([["a@0", "+", "b@1"], "+", "c@2"])
            == canon_constraint(["a@0", "+", ["b@1", "+", "c@2"]]))


def test_canon_signed_residue_equiv_unary():
    # 2013265920 * x  ==  -x  (== unary minus)
    assert (canon_constraint([2013265920, "*", "x@0"])
            == canon_constraint(["-", "x@0"]))


def test_canon_identity_folding():
    assert canon_constraint([0, "+", "x@0"]) == canon_constraint("x@0")
    assert canon_constraint(["x@0", "*", 1]) == canon_constraint("x@0")
    assert canon_constraint(["x@0", "*", 0]) == ("c", 0)


# --- build_diff -------------------------------------------------------------
def test_diff_pure_removal_and_addition():
    a = _c([["x@0", "+", 1], ["y@1", "+", 2], ["z@2", "+", 3]])
    b = _c([["x@0", "+", 1]])
    d = build_diff(a, b)
    assert len(d.removed) == 2 and not d.added and not d.changed
    d2 = build_diff(b, a)
    assert len(d2.added) == 2 and not d2.removed


def test_diff_in_place_change_is_matched():
    # same columns {x@0}, different constant -> one "changed" pair
    a = _c([["x@0", "+", 1]])
    b = _c([["x@0", "+", 7]])
    d = build_diff(a, b)
    assert len(d.changed) == 1 and not d.removed and not d.added


def test_diff_columns_with_substitution_annotation():
    a = _c([["x@0", "+", "y@1"]])
    b = _c([["x@0", "+", 5]])
    subs = [["y@1", 5]]
    d = build_diff(a, b, subs=subs)
    assert d.cols_removed == [("y@1", 5)]
    assert d.cols_added == []


def test_diff_refuses_cross_representation():
    a = _c([["x@0", "+", 2013265920]])     # constraints (residue, no '-')
    b = _m([["x@0", "-", 1]])               # machine ('-')
    with pytest.raises(DiffError, match="across representations"):
        build_diff(a, b)


def test_diff_refuses_substitutions_input():
    with pytest.raises(DiffError):
        build_diff([["x@0", 1]], _c([["x@0", "+", 1]]))


# --- rendering --------------------------------------------------------------
def _targets():
    return (Target("k", "1", "003_solver", "a.json"),
            Target("k", "1", "004_remove_trivial", "b.json"))


def test_render_diff_json_schema():
    a = _c([["x@0", "+", "y@1"]])
    b = _c([["x@0", "+", 5]])
    d = build_diff(a, b, subs=[["y@1", 5]])
    ta, tb = _targets()
    out = json.loads(render_diff(d, ta, tb, JSON))
    assert out["format"] == "constraints"
    for key in ("a", "b", "removed", "added", "changed", "columns"):
        assert key in out
    assert out["columns"]["removed"] == [{"name": "y@1", "def": "5"}]


def test_render_diff_plain_markers_and_grouping():
    a = _c([["x@0", "+", 1], 0, 0, 0])
    b = _c([["x@0", "+", 1]])
    d = build_diff(a, b)
    ta, tb = _targets()
    text = render_diff(d, ta, tb, PLAIN)
    assert "constraints: -3 +0 ~0" in text
    assert "- 0  (x3)" in text  # the three trivial zeros grouped
