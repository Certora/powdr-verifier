"""Subprocess integration with the Rust ``simplifier`` binary."""
import json
import logging
import os
import shutil
import subprocess
from pathlib import Path

from ..paths import DATA_DIR, POWDR_DUMPS_DIR, VERIFIER_DIR, data_path_for_dump
from ..smt_backends.pysmt import script
from ..utils.args import ARGS
from ..utils.stats import stats_dump
from .utils import _script_to_string, _string_to_script

_last_rust_profile_path: Path | None = None


def last_rust_profile_path() -> Path | None:
    return _last_rust_profile_path


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


def rust_profile_data_path(
    input_path: Path | None, output_path: Path | None
) -> Path | None:
    ref = input_path or output_path
    if ref is None:
        return None
    ref = ref.resolve()
    name = f"rust-cprofile-{ref.stem}.data"
    try:
        ref.relative_to(POWDR_DUMPS_DIR.resolve())
        return data_path_for_dump(ref, name)
    except ValueError:
        pass
    try:
        ref.relative_to(DATA_DIR.resolve())
        out = ref.parent / name
        out.parent.mkdir(parents=True, exist_ok=True)
        return out
    except ValueError:
        pass
    if output_path is not None:
        out = output_path.resolve().parent / name
        out.parent.mkdir(parents=True, exist_ok=True)
        return out
    out = VERIFIER_DIR / name
    out.parent.mkdir(parents=True, exist_ok=True)
    return out


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


def rust_step_action_props(step: dict) -> dict:
    """Forward rust stderr stats into report actions (skip pass name and timing duplicates)."""
    return {k: v for k, v in step.items() if k not in ("pass", "running_time")}


def _build_simplifier_cmd(
    bin_path: Path,
    rust_pipeline: str,
    *,
    timeout: float | None,
    input_path: str = "-",
    output_path: str = "-",
) -> list[str]:
    cmd = [str(bin_path)]
    if timeout is not None:
        cmd.extend(["--timeout", str(timeout)])
    if getattr(ARGS(), "pretty", False):
        cmd.append("--pretty")
    cmd.extend([input_path, rust_pipeline, output_path])
    return cmd


def _wrap_with_perf(cmd: list[str], profile_path: Path) -> list[str] | None:
    perf = shutil.which("perf")
    if perf is None:
        logging.warning("perf not found; rust profiling skipped")
        return None
    profile_path.parent.mkdir(parents=True, exist_ok=True)
    return [
        perf,
        "record",
        "-F",
        "997",
        "-g",
        "--call-graph",
        "dwarf,4096",
        "-o",
        str(profile_path),
        "--",
        *cmd,
    ]


def run_rust_pipeline(
    smt_script: script.SmtLibScript | None,
    tactic_pipeline: str,
    *,
    timeout: float | None = None,
    profile_input: Path | None = None,
    profile_output: Path | None = None,
    input_path: Path | None = None,
    output_path: Path | None = None,
    parse_output: bool = True,
) -> tuple[script.SmtLibScript | None, list[dict]]:
    global _last_rust_profile_path
    bin_path = resolve_simplifier_bin()
    if bin_path is None:
        raise FileNotFoundError("simplifier binary not found")

    rust_pipeline = ":".join(
        strip_executor(part) for part in tactic_pipeline.split(":")
    )

    use_file_input = input_path is not None
    use_file_output = output_path is not None
    smt_in: str | None = None
    if not use_file_input:
        smt_in = _script_to_string(smt_script)
    cmd = _build_simplifier_cmd(
        bin_path,
        rust_pipeline,
        timeout=timeout,
        input_path=str(input_path) if use_file_input else "-",
        output_path=str(output_path) if use_file_output else "-",
    )
    profile_path: Path | None = None
    if getattr(ARGS(), "cprofile", False):
        profile_path = rust_profile_data_path(profile_input, profile_output)
        if profile_path is not None:
            wrapped = _wrap_with_perf(cmd, profile_path)
            if wrapped is not None:
                cmd = wrapped

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

    if profile_path is not None and profile_path.is_file():
        _last_rust_profile_path = profile_path
        logging.warning(
            "Rust profile data written to %s (render: verifier/flamegraph.py %s)",
            profile_path,
            profile_path,
        )

    steps = parse_rust_stats(proc.stderr)
    for stat in steps:
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

    if not parse_output:
        return None, steps
    if use_file_output:
        with open(output_path, encoding="utf-8") as out:
            return _string_to_script(out.read()), steps
    return _string_to_script(proc.stdout), steps
