"""Subprocess integration with the Rust ``simplifier`` binary."""
import json
import logging
import os
import subprocess
from pathlib import Path

from ..smt_backends.pysmt import script
from ..utils.args import ARGS
from ..utils.stats import stats_dump
from .utils import _script_to_string, _string_to_script


def _verifier_root() -> Path:
    return Path(__file__).resolve().parents[2]


def resolve_simplifier_bin() -> Path | None:
    override = os.environ.get("SIMPLIFIER_BIN")
    if override:
        path = Path(override).expanduser()
        if path.is_file():
            return path
        logging.warning("SIMPLIFIER_BIN=%s does not exist", override)
    rust_dir = _verifier_root() / "rust"
    for profile in ("release", "debug"):
        candidate = rust_dir / "target" / profile / "simplifier"
        if candidate.is_file():
            return candidate
    return None


def parse_rust_stats(stderr: str) -> list[dict]:
    out: list[dict] = []
    for line in stderr.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return out


def strip_executor(raw_tactic: str) -> str:
    """Drop a ``p#`` / ``r#`` executor prefix before invoking Rust."""
    if len(raw_tactic) >= 2 and raw_tactic[1] == "#" and raw_tactic[0] in "pr":
        return raw_tactic[2:]
    return raw_tactic


def _pass_stats_name(pass_name: str) -> str:
    return pass_name.split("-", 1)[0]


def run_rust_pipeline(
    smt_script: script.SmtLibScript, tactic_pipeline: str
) -> script.SmtLibScript:
    bin_path = resolve_simplifier_bin()
    if bin_path is None:
        raise FileNotFoundError("simplifier binary not found")

    rust_pipeline = ":".join(
        strip_executor(part) for part in tactic_pipeline.split(":")
    )

    smt_in = _script_to_string(smt_script)
    cmd = [str(bin_path)]
    if getattr(ARGS(), "pretty", False):
        cmd.append("--pretty")
    cmd.extend(["-", rust_pipeline, "-"])
    env = os.environ.copy()
    env["SIMPLIFIER_FIELD_MOD"] = str(ARGS().field_type.value)
    proc = subprocess.run(
        cmd,
        input=smt_in,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"simplifier exited {proc.returncode}: {proc.stderr.strip()}"
        )

    for stat in parse_rust_stats(proc.stderr):
        pass_name = stat.get("pass", "rust")
        data = {k: v for k, v in stat.items() if k != "pass"}
        base = _pass_stats_name(pass_name)
        if base == "z3":
            stats_dump("z3", {"backend": "rust", **data})
        elif base == "nnf":
            stats_dump("nnf", data)
        elif base == "evaluator":
            stats_dump("evaluator", data)
        elif base == "demod":
            stats_dump("demod", data)
        elif base == "normalize":
            stats_dump("normalize", data)
        elif base == "skolem":
            stats_dump("skolem", data)
        elif base == "lift":
            stats_dump("lift_forall", data)
        elif base == "witness":
            stats_dump("witness", data)
        elif base == "bounds":
            stats_dump("bounds", data)
        elif base == "bitwise":
            stats_dump("bitwise", data)
        elif base == "mod_inv":
            stats_dump("mod_inv", data)
        elif base == "domain_probe":
            stats_dump("domain_probe", data)
        elif base == "isqf":
            stats_dump("isqf", data)
        else:
            stats_dump(base, data)

    return _string_to_script(proc.stdout)
