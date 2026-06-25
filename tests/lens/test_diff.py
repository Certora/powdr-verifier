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


# --- bus interactions -------------------------------------------------------
def _cb(bus):
    """A constraints-format dump with the given bus interactions."""
    return {"constraints": [], "bus_interactions": bus, "derived_columns": []}


def _mem(ptr, data, ts, mult=1, asp=1):
    return {"id": 1, "mult": mult, "args": [asp, ptr, *data, ts]}


_LABELS = {"1": "Memory", "6": "BitwiseLookup"}


def test_bus_memory_changed_matched_by_cell():
    # same (as=1, ptr=40), different data -> one changed pair (not -1/+1)
    a = _cb([_mem(40, ["x@0"], "t@1")])
    b = _cb([_mem(40, ["y@2"], "t@1")])
    d = build_diff(a, b, labels=_LABELS)
    assert len(d.bus_changed) == 1
    assert not d.bus_removed and not d.bus_added
    (la, _), (lb, _) = d.bus_changed[0]
    assert la == "Memory" and lb == "Memory"


def test_bus_memory_removed():
    a = _cb([_mem(40, ["x@0"], "t@1"), _mem(44, ["y@1"], "t@2")])
    b = _cb([_mem(40, ["x@0"], "t@1")])
    d = build_diff(a, b, labels=_LABELS)
    assert len(d.bus_removed) == 1 and not d.bus_added and not d.bus_changed
    assert d.bus_removed[0][0] == "Memory"


def test_bus_nonmemory_changed_via_column_proxy():
    # BitwiseLookup [x,y,z,op]; share x@0,y@1 (Jaccard 2/4 = 0.5) -> changed
    a = _cb([{"id": 6, "mult": 1, "args": ["x@0", "y@1", "w@3", 0]}])
    b = _cb([{"id": 6, "mult": 1, "args": ["x@0", "y@1", "z@4", 0]}])
    d = build_diff(a, b, labels=_LABELS)
    assert len(d.bus_changed) == 1


def test_bus_exact_unchanged_absent():
    a = _cb([_mem(40, ["x@0"], "t@1")])
    d = build_diff(a, _cb([_mem(40, ["x@0"], "t@1")]), labels=_LABELS)
    assert not d.bus_removed and not d.bus_added and not d.bus_changed


def test_render_changed_constraint_aligned_inline():
    # same shape, one leaf differs -> inline {old -> new}, not before=>after
    d = build_diff(_c([["x@0", "+", 1]]), _c([["x@0", "+", 7]]))
    text = render_diff(d, *_targets(), PLAIN)
    assert "~ (x@0 + {1 -> 7})" in text
    assert "=>" not in text  # aligned, no fallback


def test_render_changed_constraint_shape_mismatch_falls_back():
    # B's sum has an extra term -> shapes differ -> fall back to before => after
    d = build_diff(_c([["x@0", "+", 1]]), _c([["x@0", "+", ["y@1", "+", 1]]]))
    text = render_diff(d, *_targets(), PLAIN)
    assert "=>" in text


def test_render_changed_memory_aligned_inline():
    a = _cb([_mem(40, ["x@0", "x@1"], "t@9")])
    b = _cb([_mem(40, ["y@2", "x@1"], "t@9")])  # only first data limb changes
    d = build_diff(a, b, labels=_LABELS)
    text = render_diff(d, *_targets(), PLAIN)
    assert "[as=1, ptr=40]" in text
    assert "{x@0 -> y@2}" in text and "x@1" in text  # changed limb marked, rest plain


def test_render_diff_bus_summary_and_json():
    a = _cb([_mem(40, ["x@0"], "t@1"), _mem(44, ["y@1"], "t@2")])
    b = _cb([_mem(40, ["x@0"], "t@1")])
    d = build_diff(a, b, labels=_LABELS)
    ta, tb = _targets()
    text = render_diff(d, ta, tb, PLAIN)
    assert "bus: -1 +0 ~0   memory: -1 +0 ~0" in text
    out = json.loads(render_diff(d, ta, tb, JSON))
    assert out["bus"]["memory"]["removed"] == 1
    assert len(out["bus"]["removed"]) == 1
