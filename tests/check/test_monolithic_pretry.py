"""Regression: the ``check`` step tries a cheap monolithic whole-script solve
before falling back to per-disjunct chunking.

Splitting the goal ``Or`` and solving the disjuncts incrementally defeats z3's
monolithic QF_NIA/nlsat tactic and stalls for minutes on formulas the
whole-script solve refutes in milliseconds (observed on ~55/61 guest-keccak
``001_exec_bus`` steps). The pre-try must resolve those without ever chunking,
and must still fall back to chunking when the monolithic solve is inconclusive.
"""
import subprocess
import sys
from pathlib import Path

import src.checker as checker_mod
from src.checker import (
    CHECK_CHUNKED,
    CHECK_PLAIN,
    CHECK_SLICED,
    PLAIN_PRETRY_SEC,
    check_plain,
    _resolve_check_strategy,
    check,
)
from src.utils.args import parse_args

# Unsat (x is pinned to 1) with a splittable top-level Or goal.
UNSAT_OR = """
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () Int)
(assert (= x 1))
(assert (or (= x 2) (= x 3) (= x 4)))
(check-sat)
"""

# Satisfiable (x = 2 works) with a splittable top-level Or goal.
SAT_OR = """
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(assert (or (= x 2) (= x 3)))
(check-sat)
"""

# Satisfiable with pinned values, to exercise model read-back.
SAT_MODEL = """
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun flag () Bool)
(declare-fun neg () Int)
(assert (= x 7))
(assert flag)
(assert (= neg (- 3)))
(check-sat)
"""


def _solve_action(res):
    return next(a for a in res.actions if a.name == "solve")


def test_pretry_resolves_without_chunking(tmp_path, monkeypatch):
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    # ``chunked`` runs the cheap whole-script pre-try first; it must resolve the
    # goal without ever reaching the per-disjunct path.
    parse_args(["check", str(f), "--strategy", "chunked", "--timeout", "30"])

    chunked = {"called": False}
    monkeypatch.setattr(
        checker_mod,
        "check_smt_script_disjuncts",
        lambda *a, **k: chunked.__setitem__("called", True),
    )

    res = check()

    solve = _solve_action(res)
    assert solve.result == "unsat"
    # Never fell through to the pathological per-disjunct path.
    assert chunked["called"] is False
    # The solve used the short pre-try budget, not the full check timeout.
    attempt = solve.actions[0]
    assert attempt.solver_options["timeout"] == int(PLAIN_PRETRY_SEC * 1000)


def test_pretry_inconclusive_falls_back_to_chunking(tmp_path, monkeypatch):
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--strategy", "chunked", "--timeout", "30"])

    # Force the pre-try to report inconclusive.
    monkeypatch.setattr(checker_mod, "check_plain", lambda *a, **k: None)
    # Keep the fallback on the Python path (skip the Rust binary if present).
    from src.check import rust as rust_mod

    monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)

    res = check()

    # The chunked disjunct path still proves the goal unsat.
    assert _solve_action(res).result == "unsat"


def test_plain_records_unknown_not_bare_timeout(tmp_path, monkeypatch):
    """A z3 ``unknown`` on the plain strategy must be RECORDED (as
    ``unknown-timeout``, since check_plain always time-limits z3) with its solve
    attempt intact -- not discarded into a bare ``timeout`` stub. Regression: the
    stub made timed-out checks look like z3 never ran, hiding the real cause."""
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])
    from pathlib import Path

    monkeypatch.setattr(checker_mod, "_resolve_pretry_z3", lambda: Path("/bin/true"))
    monkeypatch.setattr(
        checker_mod, "communicate_with_timeout", lambda *a, **k: ("unknown\n", "", False)
    )
    res = check_plain(30, accept_inconclusive=True)
    assert res is not None, "plain must not discard an unknown into a bare stub"
    solve = _solve_action(res)
    assert solve.result == "unknown-timeout"
    # classifies as a timeout (z3 exhausted its budget), not error/success.
    assert res.status() == "timeout"


def test_pretry_accepts_sat(tmp_path):
    """A ``sat`` result is taken by the pre-try just like ``unsat``."""
    f = tmp_path / "s.smt2"
    f.write_text(SAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])
    res = check_plain()
    assert res is not None
    assert _solve_action(res).result == "sat"


def test_pretry_sat_dumps_model(tmp_path):
    """With --dump-model, the sat pre-try reads the model back and writes it."""
    import json

    f = tmp_path / "s.smt2"
    f.write_text(SAT_MODEL)
    model_path = tmp_path / "out.model"
    parse_args(["check", str(f), "--dump-model", str(model_path), "--timeout", "30"])
    res = check_plain()
    assert res is not None
    solve = _solve_action(res)
    assert solve.result == "sat"
    assert model_path.exists()
    model = json.loads(model_path.read_text())
    # x is pinned to 7, flag to true, neg to -3 in SAT_MODEL.
    assert model["x"] == 7
    assert model["flag"] is True
    assert model["neg"] == -3


def test_no_pretry_when_disabled_by_flag(tmp_path, monkeypatch):
    """``--no-pretry-plain`` skips the pre-try and goes straight to chunking."""
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--strategy", "chunked", "--no-pretry-plain", "--timeout", "30"])
    from src.check import rust as rust_mod

    monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)

    called = {"pretry": False}
    monkeypatch.setattr(
        checker_mod,
        "check_plain",
        lambda *a, **k: called.__setitem__("pretry", True) or None,
    )

    res = check()
    assert called["pretry"] is False
    assert _solve_action(res).result == "unsat"  # solved via chunking


def test_pretry_on_by_default(tmp_path):
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])
    from src.utils.args import ARGS

    assert ARGS().pretry_plain is True


def _counting_pretry(monkeypatch, calls):
    orig = checker_mod.check_plain
    monkeypatch.setattr(
        checker_mod,
        "check_plain",
        lambda *a, **k: (calls.__setitem__("n", calls["n"] + 1), orig(*a, **k))[1],
    )


def test_pretry_runs_regardless_of_strategy(tmp_path, monkeypatch):
    """The whole-script solve runs for every strategy: as the pre-try before
    ``chunked``/``sliced``, and as the ``plain`` default itself."""
    from src.check import rust as rust_mod

    for extra in (["--strategy", "chunked"], ["--strategy", "sliced"], []):
        f = tmp_path / "u.smt2"
        f.write_text(UNSAT_OR)
        parse_args(["check", str(f), *extra, "--timeout", "30"])
        monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)
        calls = {"n": 0}
        _counting_pretry(monkeypatch, calls)

        res = check()
        assert calls["n"] == 1, extra
        assert _solve_action(res).result == "unsat", extra


def test_importing_checker_does_not_break_mod_typecheck():
    """main.py imports src.checker before src.smt_backends.pysmt; a stray
    top-level pysmt.smtlib import in checker initializes the env before the
    custom MOD operator is registered, breaking MOD type-checking in the encode
    path. Run in a fresh interpreter with main.py's import order to guard that.
    """
    root = Path(__file__).resolve().parents[2]
    code = (
        "import src.checker\n"  # exactly what main.py imports first
        "from pysmt.shortcuts import Int, Equals, get_env\n"
        "m = get_env().formula_manager.Mod(Int(5), Int(3))\n"
        "assert Equals(m, Int(0)).get_type() is not None\n"
        "print('MOD_OK')\n"
    )
    r = subprocess.run(
        [sys.executable, "-c", code], cwd=root, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr
    assert "MOD_OK" in r.stdout


def test_strategy_resolution(tmp_path):
    """``plain`` is the default; only ``inlining`` overrides (to ``sliced``); an
    explicit ``--strategy`` beats both.

    The pass is taken from ``--optimization-step``, else parsed from the input
    filename so a standalone ``check`` picks the same strategy.
    """
    parse_args(["check", "x.smt2", "--optimization-step", "inlining"])
    assert _resolve_check_strategy() == CHECK_SLICED

    parse_args(["check", "x.smt2", "--optimization-step", "solver"])
    assert _resolve_check_strategy() == CHECK_PLAIN

    parse_args(["check", "x.smt2"])
    assert _resolve_check_strategy() == CHECK_PLAIN

    # Filename fallback (real verify-style name).
    fname = "verify-apc_candidate_1_0_unopt-apc_candidate_1_1_exec_bus.soundness.smt2"
    parse_args(["check", fname])
    assert _resolve_check_strategy() == CHECK_PLAIN

    # Explicit --strategy wins over the per-pass override.
    fname_inl = "verify-apc_candidate_1_0_x-apc_candidate_1_1_inlining.soundness.smt2"
    parse_args(["check", fname_inl, "--strategy", "chunked"])
    assert _resolve_check_strategy() == CHECK_CHUNKED
    parse_args(["check", "x.smt2", "--optimization-step", "inlining", "--strategy", "sliced"])
    assert _resolve_check_strategy() == "sliced"


def test_exec_bus_uses_full_budget_and_never_chunks(tmp_path, monkeypatch):
    """The ``plain`` strategy (exec_bus default) gives the whole-script solve the
    full check budget (not the short pre-try cap) and never chunks."""
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30", "--optimization-step", "exec_bus"])

    chunked = {"called": False}
    monkeypatch.setattr(
        checker_mod,
        "check_smt_script_disjuncts",
        lambda *a, **k: chunked.__setitem__("called", True),
    )

    res = check()

    solve = _solve_action(res)
    assert solve.result == "unsat"
    assert chunked["called"] is False
    # Full check timeout, not the short PLAIN_PRETRY_SEC cap.
    assert solve.actions[0].solver_options["timeout"] == int(30 * 1000)


def test_exec_bus_inconclusive_reports_timeout_without_chunking(tmp_path, monkeypatch):
    """When the monolithic solve is inconclusive, an ``exec_bus`` check reports
    ``timeout`` rather than falling back to the (never-winning) chunked path."""
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30", "--optimization-step", "exec_bus"])

    # z3 is available, but the whole-script solve cannot decide in the budget.
    monkeypatch.setattr(checker_mod, "_resolve_pretry_z3", lambda: Path("/bin/z3"))
    monkeypatch.setattr(checker_mod, "check_plain", lambda budget_sec=None, **kw: None)
    chunked = {"called": False}
    monkeypatch.setattr(
        checker_mod,
        "check_smt_script_disjuncts",
        lambda *a, **k: chunked.__setitem__("called", True),
    )

    res = check()

    assert _solve_action(res).result == "timeout"
    assert chunked["called"] is False
