import json
import re
from io import StringIO
from textwrap import dedent

import src.check.sliced as sliced_mod
import src.utils.args as args_mod
from src.check.sliced import (
    _Kind,
    _Outcome,
    _SlicedChecker,
    check_smt_script_sliced,
    flatten_script_conjuncts,
)
from src.report.action import Action
from src.smt.utils import *

BOUNDARY = re.compile(r"memory_(match|isinput|isoutput|isdisabled)")


def _parse(text: str) -> list:
    return list(SmtLibParser().get_script(StringIO(dedent(text).strip() + "\n")))


def _run(text: str, **kwargs):
    ctx, goal = flatten_script_conjuncts(_parse(text))
    assert goal is not None
    kwargs.setdefault("boundary_pattern", BOUNDARY)
    with Action("solve") as action:
        res = check_smt_script_sliced(goal, ctx, action, **kwargs)
    attempt = action.actions[0]
    return res, attempt


UNSAT_MIXED = """
    (set-logic ALL)
    (declare-fun x () Int)
    (declare-fun y () Int)
    (declare-fun memory_match_a () Bool)
    (declare-fun memory_match_b () Bool)
    (assert (= x 1))
    (assert (= y (+ x 1)))
    (assert (=> memory_match_a (= y 2)))
    (assert (or memory_match_a memory_match_b))
    (assert (not memory_match_b))
    (assert (or (= y 3) (and memory_match_a memory_match_b) (= y 0)))
    (check-sat)
"""


def test_flatten_script_conjuncts():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (and (= x 1) (and (> x 0) (> x 0))))
        (assert (or (= x 2) (= x 3) (= x 4)))
        (check-sat)
        """
    )
    ctx, goal = flatten_script_conjuncts(smt_script)
    x = Symbol("x", INT)
    # nested Ands flattened, duplicate (> x 0) deduped, goal excluded
    assert ctx == [Equals(x, Int(1)), GT(x, Int(0))]
    assert goal.is_or() and len(goal.args()) == 3


def test_flatten_no_goal():
    ctx, goal = flatten_script_conjuncts(
        _parse("(set-logic ALL)(declare-fun x () Int)(assert (= x 1))(check-sat)")
    )
    assert goal is None and len(ctx) == 1


def test_arith_and_mem_refute():
    """Arith disjuncts close on the boundary-stopped slice; the memory-only
    disjunct closes on the shared memory-argument solver."""
    res, attempt = _run(UNSAT_MIXED)
    assert res == "unsat"
    assert attempt.properties["tiers"]["arith"] == 2
    assert attempt.properties["tiers"]["mem"] == 1
    assert attempt.properties["n_mem_constraints"] == 3


def test_cegar_refute():
    """Slice-sat model falsifies an omitted memory constraint; CEGAR adds it
    and refutes without escalating."""
    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun memory_match_a () Bool)
        (assert (or (= x 0) memory_match_a))
        (assert (not memory_match_a))
        (assert (or (= x 1) (= x 2) (= x 3)))
        (check-sat)
        """
    )
    assert res == "unsat"
    assert attempt.properties["tiers"]["arith+cegar"] == 3
    counters = attempt.properties["metrics"]["counters"]
    assert counters["cegar_constraints_added"] >= 3


def test_escalation_to_union_slice():
    """The slice model leaves omitted constraints undetermined (no falsified
    ones), so the ladder escalates to slice ∪ memory-argument."""
    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun memory_match_a () Bool)
        (assert (or memory_match_a (< x 3)))
        (assert (or (not memory_match_a) (< y 3)))
        (assert (= y 10))
        (assert (or (> x 5) (> x 6) (> x 7)))
        (check-sat)
        """
    )
    assert res == "unsat"
    tiers = attempt.properties["tiers"]
    # The first disjunct escalates (undetermined omitted constraints); the
    # learned Not(d) then lets the remaining ones close on the arith rung.
    assert sum(n for t, n in tiers.items() if t.startswith("escalated")) >= 1
    assert attempt.properties["metrics"]["counters"]["escalations_to_mem_union"] >= 1
    assert attempt.properties["hard_disjuncts"] == [0]
    assert sum(tiers.values()) == 3


def test_genuine_sat_canary():
    """SOUNDNESS CANARY: a satisfiable VC must come back sat (never unsat),
    with a model that satisfies every context conjunct."""
    text = """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun memory_match_a () Bool)
        (assert (= y (+ x 1)))
        (assert (or memory_match_a (= x 0)))
        (assert (or (= y 3) (= y 100) (= y 7)))
        (check-sat)
    """
    res, attempt = _run(text, debug=True)
    assert res == "sat"
    assert attempt.properties["disjunct_index"] is not None
    model = attempt.properties["model"]
    assert model
    ctx, _ = flatten_script_conjuncts(_parse(text))
    subs = {
        Symbol(k, BOOL if isinstance(v, bool) else INT): Bool(v) if isinstance(v, bool) else Int(v)
        for k, v in model.items()
    }
    for c in ctx:
        assert substitute_no_validate(c, subs).simplify().is_true(), c


def test_syntactic_discharge():
    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= x 1))
        (assert (or (< 2 1) (= x 2) (= x 3)))
        (check-sat)
        """
    )
    assert res == "unsat"
    assert attempt.properties["tiers"]["syntactic"] == 1


def test_dedupe_identical_disjuncts():
    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= x 1))
        (assert (or (= x 2) (= x 2) (= x 3)))
        (check-sat)
        """
    )
    assert res == "unsat"
    assert attempt.properties["tiers"]["cached"] == 1
    assert attempt.properties["tiers"]["arith"] == 2


def _force_unknown_on(monkeypatch, target_index: int):
    """Make every rung return UNKNOWN for disjunct ``target_index``."""
    original = _SlicedChecker._solve_under

    def fake(self, s, k, d, **kwargs):
        if k == target_index:
            return _Outcome(_Kind.UNKNOWN, reason="canceled")
        return original(self, s, k, d, **kwargs)

    monkeypatch.setattr(_SlicedChecker, "_solve_under", fake)


def test_unknown_fail_fast(monkeypatch):
    _force_unknown_on(monkeypatch, target_index=1)
    res, attempt = _run(UNSAT_MIXED)
    assert res == "unknown-canceled"
    assert attempt.properties["disjunct_index"] == 1


def test_unknown_collect_mode(monkeypatch):
    _force_unknown_on(monkeypatch, target_index=1)
    res, attempt = _run(UNSAT_MIXED, collect_unknowns=-1)
    assert res == "unknown"
    assert attempt.properties["unknown_disjuncts"] == [{"index": 1, "reason": "canceled"}]
    # the other disjuncts were still visited and refuted
    tiers = attempt.properties["tiers"]
    assert sum(tiers.values()) == 2


def test_boundary_regex_override():
    """With a boundary that matches nothing, everything is one plain COI
    slice -- no memory rung, no boundary vars."""
    res, attempt = _run(UNSAT_MIXED, boundary_pattern=re.compile(r"\bnothing\b"))
    assert res == "unsat"
    assert attempt.properties["n_boundary_vars"] == 0
    assert attempt.properties["n_mem_constraints"] == 0
    assert "mem" not in attempt.properties["tiers"]


def test_dump_slices_rerunnable(tmp_path):
    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun memory_match_a () Bool)
        (assert (or (= x 0) memory_match_a))
        (assert (not memory_match_a))
        (assert (or (= x 1) (= x 2) (= x 3)))
        (check-sat)
        """,
        dump_dir=tmp_path,
    )
    assert res == "unsat"
    manifest = json.loads((tmp_path / "manifest.json").read_text())
    assert manifest, "interesting queries (cegar rounds) must be dumped"
    for record in manifest:
        smt_script = list(SmtLibParser().get_script_fname(str(tmp_path / record["file"])))
        with Solver(name=ARGS().solver, logic=ALL) as s:
            s.set_logic = lambda l: None
            for cmd in smt_script:
                if cmd.name == "assert":
                    s.add_assertion(cmd.args[0])
            assert s.solve() == (record["result"] == "sat")


def test_growing_solver_amortizes_asserts():
    """Batches with overlapping slices share the growing solver: each ctx
    constraint is asserted once (delta), not once per batch."""
    res, attempt = _run(UNSAT_MIXED)
    assert res == "unsat"
    assert attempt.properties["tiers"]["arith"] == 2
    counters = attempt.properties["metrics"]["counters"]
    # the two arith disjuncts share one slice; its 3 constraints are
    # asserted exactly once
    assert counters["grow_delta_asserted"] == 3
    assert "grow_gc_restarts" not in counters


def test_growing_solver_gc():
    """When the resident context exceeds gc_factor x the current slice, the
    growing solver is restarted and repopulated."""
    from src.check.sliced import SliceBudgets

    res, attempt = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun w () Int)
        (declare-fun v () Int)
        (declare-fun z () Int)
        (assert (= z 5))
        (assert (= x 1))
        (assert (= y (+ x 1)))
        (assert (= w (+ y 1)))
        (assert (= v (+ w 1)))
        (assert (or (= z 6) (= v 100) (= x 2)))
        (check-sat)
        """,
        budgets=SliceBudgets(gc_factor=1.2),
    )
    assert res == "unsat"
    assert attempt.properties["tiers"]["arith"] == 3
    counters = attempt.properties["metrics"]["counters"]
    # tiny z-slice first (ascending), then the 4-constraint chain slice:
    # 1 + 4 > 1.2 * 4 forces a GC restart
    assert counters["grow_gc_restarts"] == 1
    assert counters["grow_delta_asserted"] == 5


def test_write_query_declares_uninterpreted_functions(tmp_path):
    """Serialized queries must declare UF symbols with their arity --
    a 0-ary declare-fun for uf_and(x,y) makes z3 error-skip every
    uf-bearing assert (observed on 2100224's bitwise disjuncts)."""
    from src.check.sliced import _write_query

    x = Symbol("x", INT)
    uf = Symbol("uf_and", FunctionType(INT, [INT, INT]))
    f = Equals(Function(uf, [x, Int(3)]), Int(5))
    path = tmp_path / "q.smt2"
    _write_query(path, [f], "(check-sat)")
    text = path.read_text()
    assert "(declare-fun uf_and (Int Int) Int)" in text
    # must re-parse cleanly
    reparsed = SmtLibParser().get_script(StringIO(text))
    asserts = [c.args[0] for c in reparsed if c.name == "assert"]
    assert asserts == [f]


def test_metrics_consistency():
    res, attempt = _run(UNSAT_MIXED)
    assert res == "unsat"
    tiers = attempt.properties["tiers"]
    assert sum(tiers.values()) == attempt.properties["n_disjuncts"]
    metrics = attempt.properties["metrics"]
    assert metrics["counters"]["n_slice_groups"] >= 1
    assert "solve_arith" in metrics["timing_s"]
    assert metrics["distributions"]["slice_size"]["count"] >= 1


def test_dispatch_bypasses_rust(tmp_path, monkeypatch):
    """--solve-sliced must never delegate to the Rust checker binary."""
    from src import checker as checker_mod
    from src.check import rust as rust_mod

    vc = tmp_path / "vc.smt2"
    vc.write_text(
        dedent(
            """
            (set-logic ALL)
            (set-info :status unsat)
            (declare-fun x () Int)
            (assert (= x 1))
            (assert (or (= x 2) (= x 3) (= x 4)))
            (check-sat)
            """
        ).strip()
        + "\n"
    )
    calls = []
    monkeypatch.setattr(
        rust_mod, "resolve_checker_bin", lambda: calls.append("resolve") or None
    )
    saved = args_mod.__dict__.get("__ARGS")
    # Disable the monolithic pre-try so the sliced dispatch is what runs here.
    args_mod.parse_args(["check", str(vc), "--solve-sliced", "--no-monolithic-pretry"])
    try:
        action = checker_mod.check()
    finally:
        args_mod.__dict__["__ARGS"] = saved
    assert calls == [], "rust checker must not be consulted in sliced mode"
    solve = action.actions[-1]
    assert solve.result == "unsat"
    assert solve.actions[0].properties.get("mode") == "sliced"


def test_preempt_and_sticky_fallback_preference(monkeypatch):
    """The preempt preference reaches only the immediate neighbor (a stale
    preempt makes every easy disjunct pay a one-shot subprocess), while the
    sticky fallback-ordering memory survives interleaved plain wins."""
    seen = {}

    def fake_ladder(self, group_solver, k, d, primary_rung,
                    primary_considered, slice_idx, *, prefer=None, fallback=None):
        seen[k] = (prefer, fallback)
        return "arith", _Outcome(_Kind.REFUTED, via="closed" if k == 0 else None)

    monkeypatch.setattr(_SlicedChecker, "_ladder", fake_ladder)
    res, _ = _run(
        """
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (= x 0))
        (assert (or (= x 1) (= x 2) (= x 3)))
        (check-sat)
        """
    )
    assert res == "unsat"
    # d0 wins via closed -> d1 gets the preempt; d1's plain win clears the
    # preempt for d2 but the sticky fallback survives.
    assert seen == {
        0: (None, None),
        1: ("closed", "closed"),
        2: (None, "closed"),
    }


def test_preference_hit_miss_counters(monkeypatch):
    """prefer_hit / prefer_miss count whether the locality guess paid off,
    so a noisy preference is visible in the report."""
    from src.check.sliced import Metrics, SliceBudgets

    ctx, goal = flatten_script_conjuncts(
        _parse(
            """
            (set-logic ALL)
            (declare-fun x () Int)
            (assert (= x 0))
            (assert (or (= x 1) (= x 2)))
            (check-sat)
            """
        )
    )
    metrics = Metrics()
    checker = _SlicedChecker(
        ctx,
        goal,
        budgets=SliceBudgets(),
        boundary_pattern=BOUNDARY,
        metrics=metrics,
        dumper=None,
        collect_unknowns=None,
        debug=False,
    )
    try:
        d0, d1 = checker.disjuncts
        s, considered = checker.grow_solver_for(frozenset({0}))
        # preferred one-shot misses (returns unknown) -> incremental refutes
        monkeypatch.setattr(_SlicedChecker, "_try_strategy", lambda self, *a: None)
        out = checker._solve_under(s, 0, d0, rung="arith", considered=considered,
                                   prefer="closed")
        assert out.kind is _Kind.REFUTED and out.via is None
        # preferred one-shot hits (returns unsat)
        monkeypatch.setattr(_SlicedChecker, "_try_strategy", lambda self, *a: False)
        out = checker._solve_under(s, 1, d1, rung="arith", considered=considered,
                                   prefer="closed")
        assert out.kind is _Kind.REFUTED and out.via == "closed"
    finally:
        checker.close()
    counters = metrics.as_dict()["counters"]
    assert counters["prefer_miss"] == 1
    assert counters["prefer_hit"] == 1
