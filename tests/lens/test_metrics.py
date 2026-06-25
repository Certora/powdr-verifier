"""Expression-tree metrics and multiplicity classification."""
from src.lens.loader import detect_format
from src.lens.metrics import NEG_ONE, DumpStats, analyze_expr, mult_kind


def test_constant_and_column():
    c = analyze_expr(7)
    assert (c.nodes, c.depth, c.degree, c.columns) == (1, 1, 0, set())
    col = analyze_expr("x@1")
    assert (col.nodes, col.degree, col.columns) == (1, 1, {"x@1"})


def test_infix_product_degree_and_ops():
    # x@1 * (x@1 - 1)  -> degree 2 (a product), columns {x@1}
    info = analyze_expr(["x@1", "*", ["x@1", "-", 1]])
    assert info.degree == 2
    assert info.columns == {"x@1"}
    assert info.ops["*"] == 1 and info.ops["-"] == 1
    assert info.nodes == 5  # 2 cols + 1 const + 2 ops


def test_addition_takes_max_degree():
    info = analyze_expr([["x@1", "*", "y@2"], "+", "z@3"])
    assert info.degree == 2  # product term dominates the sum
    assert info.columns == {"x@1", "y@2", "z@3"}


def test_unary_negation_preserves_degree():
    info = analyze_expr(["-", ["x@1", "+", "y@2"]])
    assert info.degree == 1
    assert info.columns == {"x@1", "y@2"}
    assert info.ops["-"] == 1 and info.ops["+"] == 1


def test_bool_is_constant_not_int():
    info = analyze_expr(True)  # bool subclasses int; must not be read as 1
    assert info.degree == 0 and info.nodes == 1


def test_bag_list_not_misread_as_infix():
    # A QuotientOrZero value [num, den] is a 2-tuple of expressions, NOT an
    # infix [lhs, op, rhs]. Must not crash and must collect both columns.
    info = analyze_expr({"QuotientOrZero": ["n@0", ["d@1", "*", "d@1"]]})
    assert info.columns == {"n@0", "d@1"}
    assert info.degree == 2  # max over the bag (d@1*d@1)


def test_mult_kind():
    assert mult_kind(1) == "send"
    assert mult_kind(NEG_ONE) == "recv"
    assert mult_kind(-1) == "recv"
    assert mult_kind(2) == "other"
    assert mult_kind(True) == "other"  # bool before int
    assert mult_kind("a@5") == "sym"
    assert mult_kind(["a@5", "+", 1]) == "sym"
    # column-free expressions are concrete, not symbolic
    assert mult_kind(["-", 1]) == "recv"      # unary minus of 1 = -1
    assert mult_kind(["-", ["-", 1]]) == "send"  # = +1
    assert mult_kind([2, "*", 3]) == "other"  # = 6
    assert mult_kind([1, "+", "x@0"]) == "sym"


def _machine(constraints, bus=None, derived=None):
    return {
        "constraints": constraints,
        "bus_interactions": bus or [],
        "derived_columns": derived or [],
    }


def test_dumpstats_counts_and_buses():
    data = _machine(
        constraints=[["f@0", "*", ["f@0", "-", 1]], "g@1"],
        bus=[
            {"id": 1, "mult": 1, "args": ["a@0", ["b@1", "+", 1]]},
            {"id": 1, "mult": NEG_ONE, "args": []},
            {"id": 3, "mult": "sel@2", "args": []},
        ],
        derived=[[True, "q@9", {"QuotientOrZero": ["n@0", "d@1"]}]],
    )
    s = DumpStats.from_data(data, {"1": "Memory", "3": "RangeChecker"})
    assert s.n_constraints == 2
    assert s.n_bus_interactions == 3
    assert s.n_derived_columns == 1
    assert s.degree.max == 2  # the booleanity constraint
    assert s.derived_forms["QuotientOrZero"] == 1
    mem = next(r for r in s.buses if r.id == "1")
    assert (mem.count, mem.send, mem.recv, mem.label) == (2, 1, 1, "Memory")
    rc = next(r for r in s.buses if r.id == "3")
    assert (rc.sym, rc.label) == (1, "RangeChecker")


def test_detect_format():
    # base dump (block/subs) -> machine (algebraic, with context)
    assert detect_format({"block": {}, "machine": {}, "subs": []}) == "machine"
    assert detect_format({"subs": []}) == "machine"
    # step with a "-" operator (algebraic encoding) -> machine
    assert detect_format(
        {"constraints": [["f@0", "-", 1]], "bus_interactions": []}) == "machine"
    # step with only field residue, no "-" -> constraints (grouped)
    assert detect_format(
        {"constraints": [["f@0", "+", 2013265920]], "bus_interactions": []}
    ) == "constraints"
    # the substitutions list artifact
    assert detect_format([["x@0", 1], ["y@1", 2]]) == "substitutions"
    assert detect_format({}) == "unknown"


def test_dumpstats_format_field():
    # grouped step (residue, no "-") -> constraints
    step = DumpStats.from_data(
        _machine([["f@0", "+", 2013265920]], []), {})
    assert step.fmt == "constraints"
    base = DumpStats.from_data(
        {"block": {"blocks": []}, "subs": [], "machine": _machine([], [])}, {}
    )
    assert base.fmt == "machine"


def test_dumpstats_base_extras():
    base = {
        "block": {"blocks": [{"instructions": [[1], [2], [3]]}]},
        "subs": [[0, 1], [0, 1, 2]],
        "machine": _machine(constraints=[], bus=[]),
    }
    s = DumpStats.from_data(base, {})
    assert s.n_blocks == 1
    assert s.n_instructions == 3
    assert s.submachine_polys == [2, 3]
