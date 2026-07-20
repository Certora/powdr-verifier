"""Regression: the ``check`` step tries a cheap monolithic whole-script solve
before falling back to per-disjunct chunking.

Splitting the goal ``Or`` and solving the disjuncts incrementally defeats z3's
monolithic QF_NIA/nlsat tactic and stalls for minutes on formulas the
whole-script solve refutes in milliseconds (observed on ~55/61 guest-keccak
``001_exec_bus`` steps). The pre-try must resolve those without ever chunking,
and must still fall back to chunking when the monolithic solve is inconclusive.
"""
import src.checker as checker_mod
from src.checker import MONOLITHIC_PRETRY_SEC, _monolithic_pretry, check
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
    parse_args(["check", str(f), "--timeout", "30"])

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
    assert attempt.solver_options["timeout"] == int(MONOLITHIC_PRETRY_SEC * 1000)


def test_pretry_inconclusive_falls_back_to_chunking(tmp_path, monkeypatch):
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])

    # Force the pre-try to report inconclusive.
    monkeypatch.setattr(checker_mod, "_monolithic_pretry", lambda: None)
    # Keep the fallback on the Python path (skip the Rust binary if present).
    from src.check import rust as rust_mod

    monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)

    res = check()

    # The chunked disjunct path still proves the goal unsat.
    assert _solve_action(res).result == "unsat"


def test_pretry_accepts_sat(tmp_path):
    """A ``sat`` result is taken by the pre-try just like ``unsat``."""
    f = tmp_path / "s.smt2"
    f.write_text(SAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])
    res = _monolithic_pretry()
    assert res is not None
    assert _solve_action(res).result == "sat"


def test_pretry_sat_dumps_model(tmp_path):
    """With --dump-model, the sat pre-try reads the model back and writes it."""
    import json

    f = tmp_path / "s.smt2"
    f.write_text(SAT_MODEL)
    model_path = tmp_path / "out.model"
    parse_args(["check", str(f), "--dump-model", str(model_path), "--timeout", "30"])
    res = _monolithic_pretry()
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
    """``--no-monolithic-pretry`` skips the pre-try and goes straight to chunking."""
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--no-monolithic-pretry", "--timeout", "30"])
    from src.check import rust as rust_mod

    monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)

    called = {"pretry": False}
    monkeypatch.setattr(
        checker_mod,
        "_monolithic_pretry",
        lambda: called.__setitem__("pretry", True) or None,
    )

    res = check()
    assert called["pretry"] is False
    assert _solve_action(res).result == "unsat"  # solved via chunking


def test_pretry_on_by_default(tmp_path):
    f = tmp_path / "u.smt2"
    f.write_text(UNSAT_OR)
    parse_args(["check", str(f), "--timeout", "30"])
    from src.utils.args import ARGS

    assert ARGS().monolithic_pretry is True


def _counting_pretry(monkeypatch, calls):
    orig = checker_mod._monolithic_pretry
    monkeypatch.setattr(
        checker_mod,
        "_monolithic_pretry",
        lambda: (calls.__setitem__("n", calls["n"] + 1), orig())[1],
    )


def test_pretry_runs_regardless_of_strategy(tmp_path, monkeypatch):
    """The pre-try runs independently of --solve-chunked / --solve-sliced."""
    from src.check import rust as rust_mod

    for extra in (["--no-solve-chunked"], ["--solve-sliced"], []):
        f = tmp_path / "u.smt2"
        f.write_text(UNSAT_OR)
        parse_args(["check", str(f), *extra, "--timeout", "30"])
        monkeypatch.setattr(rust_mod, "resolve_checker_bin", lambda: None)
        calls = {"n": 0}
        _counting_pretry(monkeypatch, calls)

        res = check()
        assert calls["n"] == 1, extra
        assert _solve_action(res).result == "unsat", extra
