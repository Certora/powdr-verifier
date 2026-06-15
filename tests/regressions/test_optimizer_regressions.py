import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import pytest


WORKSPACE = Path(__file__).resolve().parents[3]
VERIFIER = WORKSPACE / "verifier"
POWDR_DUMPS = VERIFIER / "powdr-dumps"
MAIN = VERIFIER / "main.py"
PYTHON = VERIFIER / ".venv" / "bin" / "python"
TACTIC = "nnf:skolem:lift:witness:z3-propagate-values:isqf:bounds:rewrite:bitwise:mod_inv:demod:domain_probe:pretty"


@dataclass(frozen=True)
class RegressionCase:
    optimizer: str
    dataset: str
    block: str
    before: str
    after: str
    check: str

    @property
    def id(self) -> str:
        return f"{self.optimizer}-{self.dataset}-{self.block}-{self.check}"


CASES = [
    RegressionCase("exec_bus", "guest-keccak", "2106172", "apc_candidate_2106172_000_unopt", "apc_candidate_2106172_001_exec_bus", "soundness"),
    RegressionCase("exec_bus", "guest-keccak", "2106456", "apc_candidate_2106456_000_unopt", "apc_candidate_2106456_001_exec_bus", "soundness"),
    RegressionCase("inlining", "guest-keccak", "2106172", "apc_candidate_2106172_031_low_degree_bus", "apc_candidate_2106172_032_inlining", "completeness"),
    RegressionCase("inlining", "guest-keccak", "2106456", "apc_candidate_2106456_031_low_degree_bus", "apc_candidate_2106456_032_inlining", "completeness"),
    RegressionCase("loop_iteration", "guest-keccak", "2106172", "apc_candidate_2106172_011_low_degree_bus", "apc_candidate_2106172_012_loop_iteration", "soundness"),
    RegressionCase("loop_iteration", "reth-selection", "2702740", "apc_candidate_2702740_012_low_degree_bus", "apc_candidate_2702740_013_loop_iteration", "soundness"),
    RegressionCase("low_degree_bus", "guest-keccak", "2106172", "apc_candidate_2106172_030_memory", "apc_candidate_2106172_031_low_degree_bus", "completeness"),
    RegressionCase("low_degree_bus", "guest-keccak", "2099672", "apc_candidate_2099672_030_memory", "apc_candidate_2099672_031_low_degree_bus", "soundness"),
    RegressionCase("memory", "guest-keccak", "2106172", "apc_candidate_2106172_029_substitute_bus_interactio_fields", "apc_candidate_2106172_030_memory", "soundness"),
    RegressionCase("memory", "guest-keccak", "2106456", "apc_candidate_2106456_029_substitute_bus_interactio_fields", "apc_candidate_2106456_030_memory", "soundness"),
    RegressionCase("range_constraints", "guest-keccak", "2106456", "apc_candidate_2106456_034_rule_based", "apc_candidate_2106456_035_range_constraints", "soundness"),
    RegressionCase("range_constraints", "guest-keccak", "2106172", "apc_candidate_2106172_034_rule_based", "apc_candidate_2106172_035_range_constraints", "soundness"),
    RegressionCase("remove_disconnected", "guest-keccak", "2106456", "apc_candidate_2106456_032_inlining", "apc_candidate_2106456_033_remove_disconnected", "soundness"),
    RegressionCase("remove_disconnected", "guest-keccak", "2106172", "apc_candidate_2106172_032_inlining", "apc_candidate_2106172_033_remove_disconnected", "completeness"),
    RegressionCase("remove_free", "guest-keccak", "2106172", "apc_candidate_2106172_014_remove_trivial", "apc_candidate_2106172_015_remove_free", "soundness"),
    RegressionCase("remove_free", "guest-keccak", "2106456", "apc_candidate_2106456_024_remove_trivial", "apc_candidate_2106456_025_remove_free", "completeness"),
    RegressionCase("remove_trivial", "guest-keccak", "2106456", "apc_candidate_2106456_023_solver", "apc_candidate_2106456_024_remove_trivial", "soundness"),
    RegressionCase("remove_trivial", "guest-keccak", "2106172", "apc_candidate_2106172_023_solver", "apc_candidate_2106172_024_remove_trivial", "completeness"),
    RegressionCase("rule_based", "guest-keccak", "2106456", "apc_candidate_2106456_033_remove_disconnected", "apc_candidate_2106456_034_rule_based", "soundness"),
    RegressionCase("rule_based", "guest-keccak", "2106172", "apc_candidate_2106172_033_remove_disconnected", "apc_candidate_2106172_034_rule_based", "soundness"),
    RegressionCase("simplify_exhaustive", "reth-selection", "2702740", "apc_candidate_2702740_017_remove_disconnected", "apc_candidate_2702740_018_simplify_exhaustive", "soundness"),
    RegressionCase("simplify_exhaustive", "reth-selection", "2702740", "apc_candidate_2702740_006_remove_disconnected", "apc_candidate_2702740_007_simplify_exhaustive", "soundness"),
    RegressionCase("solver", "guest-keccak", "2106456", "apc_candidate_2106456_022_loop_iteration", "apc_candidate_2106456_023_solver", "soundness"),
    RegressionCase("solver", "reth-selection", "2702740", "apc_candidate_2702740_013_loop_iteration", "apc_candidate_2702740_014_solver", "soundness"),
    RegressionCase("substitute_bus_interactio_fields", "guest-keccak", "2106172", "apc_candidate_2106172_028_rule_based", "apc_candidate_2106172_029_substitute_bus_interactio_fields", "completeness"),
    RegressionCase("substitute_bus_interactio_fields", "guest-keccak", "2106456", "apc_candidate_2106456_018_rule_based", "apc_candidate_2106456_019_substitute_bus_interactio_fields", "completeness"),
    RegressionCase("trivial_simp", "guest-keccak", "2106456", "apc_candidate_2106456_035_range_constraints", "apc_candidate_2106456_036_trivial_simp", "soundness"),
    RegressionCase("trivial_simp", "guest-keccak", "2106172", "apc_candidate_2106172_035_range_constraints", "apc_candidate_2106172_036_trivial_simp", "soundness"),
]


def run(command: list[str | Path], timeout: int = 60) -> dict:
    completed = subprocess.run(
        [str(part) for part in command],
        cwd=WORKSPACE,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    assert completed.returncode == 0, completed.stderr + completed.stdout
    return json.loads(completed.stdout)

def run_checked(command: list[str | Path], timeout: int = 60) -> None:
    completed = subprocess.run(
        [str(part) for part in command],
        cwd=WORKSPACE,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    assert completed.returncode == 0, completed.stderr + completed.stdout


@pytest.mark.parametrize("case", CASES, ids=[case.id for case in CASES])
def test_optimizer_regression(case: RegressionCase):
    data_dir = POWDR_DUMPS / case.dataset
    if not data_dir.exists():
        pytest.skip(f"missing benchmark data: {data_dir}")

    base = data_dir / f"apc_candidate_{case.block}_000_unopt.json"
    substitutions = data_dir / f"apc_candidate_{case.block}_substitutions.json"
    before = data_dir / f"{case.before}.json"
    after = data_dir / f"{case.after}.json"
    for path in [base, substitutions, before, after]:
        assert path.exists(), path

    with tempfile.TemporaryDirectory(prefix=".tmp-regression-", dir=WORKSPACE) as tmp:
        prefix = Path(tmp) / "case"
        run([PYTHON if PYTHON.exists() else sys.executable, MAIN, "--base-dump", base, "--substitutions", substitutions, "verify", before, after, prefix])

        smt = prefix.with_suffix(f".{case.check}.smt2")
        simplified = prefix.with_suffix(f".{case.check}.rewrite.smt2")
        run([PYTHON if PYTHON.exists() else sys.executable, MAIN, "simplify", smt, TACTIC, simplified])

        result = run([PYTHON if PYTHON.exists() else sys.executable, MAIN, "check", simplified])
        assert result["__Action"]["result"] == "unsat"


@dataclass(frozen=True)
class ReplayCase:
    dataset: str
    block: str
    optimizer_pass: str
    before: str
    after: str

    @property
    def id(self) -> str:
        return f"{self.dataset}-{self.block}-{self.optimizer_pass}"


REPLAY_CASES = [
    ReplayCase(
        "guest-keccak",
        "2106172",
        "exec_bus",
        "apc_candidate_2106172_000_unopt",
        "apc_candidate_2106172_001_exec_bus",
    ),
    ReplayCase(
        "guest-keccak",
        "2106456",
        "inlining",
        "apc_candidate_2106456_031_low_degree_bus",
        "apc_candidate_2106456_032_inlining",
    ),
    ReplayCase(
        "select",
        "2099448",
        "rule_based",
        "apc_candidate_2099448_008_trivial_simp",
        "apc_candidate_2099448_009_rule_based",
    ),
]


@pytest.mark.parametrize("case", REPLAY_CASES, ids=[case.id for case in REPLAY_CASES])
def test_orchestrate_powdr_opt_replay_matches_pipeline(case: ReplayCase):
    data_dir = POWDR_DUMPS / case.dataset
    if not data_dir.exists():
        pytest.skip(f"missing benchmark data: {data_dir}")

    base = data_dir / f"apc_candidate_{case.block}_000_unopt.json"
    before = data_dir / f"{case.before}.json"
    after = data_dir / f"{case.after}.json"
    for path in [base, before, after]:
        assert path.exists(), path

    with tempfile.TemporaryDirectory(prefix=".tmp-opt-replay-", dir=WORKSPACE) as tmp:
        tmp_dir = Path(tmp)
        replay_output = tmp_dir / "replay.json"

        run_checked(
            [
                PYTHON if PYTHON.exists() else sys.executable,
                MAIN,
                "powdr-opt",
                before,
                case.optimizer_pass,
                replay_output,
                "--base-dump",
                base,
            ],
            timeout=60,
        )

        with open(replay_output, "r") as replay_file:
            replay_data = json.load(replay_file)
        with open(after, "r") as after_file:
            after_data = json.load(after_file)
        assert replay_data == after_data
