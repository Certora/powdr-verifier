"""Subprocess integration with the Rust ``simplifier`` binary."""
import json
import logging
import os
import re
import shutil
import subprocess
from pathlib import Path

from ..paths import DATA_DIR, POWDR_DUMPS_DIR, VERIFIER_DIR, data_path_for_dump
from ..smt_backends.pysmt import script, solver_command
from ..utils.args import ARGS
from ..utils.io import SMT_ENCODING
from ..utils.stats import stats_dump
from .utils import _bytes_to_script, _script_to_bytes, _string_to_script

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
    dump_steps: bool = False,
    dump_step_offset: int = 0,
    dump_steps_output: Path | None = None,
) -> list[str]:
    cmd = [str(bin_path)]
    if timeout is not None:
        cmd.extend(["--timeout", str(timeout)])
    if getattr(ARGS(), "pretty", False):
        cmd.append("--pretty")
    if dump_steps:
        cmd.append("--dump-steps")
        if dump_step_offset:
            cmd.extend(["--dump-step-offset", str(dump_step_offset)])
        if dump_steps_output is not None:
            cmd.extend(["--dump-steps-output", str(dump_steps_output)])
    cmd.extend([input_path, rust_pipeline, output_path])
    return cmd


def _perf_report_timeout_sec(profile_path: Path) -> float:
    size_mb = profile_path.stat().st_size / (1024 * 1024)
    return min(300.0, 45.0 + size_mb * 0.5)


_PERF_SYMBOL_ROW = re.compile(
    r"^\s+"
    r"(?:(?P<children>\d+\.\d+%)\s+)?"
    r"(?P<self>\d+\.\d+%)\s+"
    r"(?P<samples>\d+)\s+"
    r"\[(?P<space>[^\]]+)\]\s+"
    r"(?P<symbol>.+?)"
    r"(?:\s{2,}-.+)?$"
)


def _is_useful_perf_symbol(symbol: str, space: str) -> bool:
    if space == "k":
        return False
    sym = symbol.strip()
    if not sym or sym.endswith("@plt"):
        return False
    if re.fullmatch(r"0x[0-9a-fA-F]+", sym):
        return False
    if re.fullmatch(r"0xffffffff[0-9a-fA-F]+", sym):
        return False
    return True


def _parse_perf_symbol_row(line: str) -> str | None:
    m = _PERF_SYMBOL_ROW.match(line.rstrip())
    if m is None:
        return None
    if not _is_useful_perf_symbol(m.group("symbol"), m.group("space")):
        return None
    return f"{m.group('self')}  {m.group('symbol').strip()}"


def _format_perf_report_summary(stdout: str, *, top_n: int) -> list[str]:
    meta: list[str] = []
    rows: list[str] = []
    in_table = False
    for line in stdout.splitlines():
        if line.startswith("#"):
            stripped = line.lstrip("# ").strip()
            if stripped.startswith(("Total Lost Samples:", "Samples:", "Event count")):
                meta.append(stripped)
            if "Symbol" in stripped and ("Overhead" in stripped or "Self" in stripped):
                in_table = True
            continue
        if not in_table:
            continue
        if not line.strip() or line.lstrip().startswith("|"):
            if rows:
                break
            continue
        if line.strip().startswith("(") or re.fullmatch(r"[.\s]+", line):
            continue
        parsed = _parse_perf_symbol_row(line)
        if parsed is None:
            continue
        rows.append(parsed)
        if len(rows) >= top_n:
            break
    return meta + rows


def _emit_rust_pass_timings(steps: list[dict]) -> None:
    timed = [
        (step.get("pass", "?"), step["running_time"])
        for step in steps
        if step.get("running_time") is not None
    ]
    if not timed:
        return
    logging.warning("rust simplifier pass timings:")
    for name, running_time in timed:
        logging.warning("  %s: %.3fs", name, running_time)


def emit_perf_profile_summary(
    profile_path: Path, *, top_n: int = 12, timeout_sec: float | None = None
) -> None:
    """Run ``perf report`` and log a short symbol summary to stderr."""
    perf = shutil.which("perf")
    if perf is None or not profile_path.is_file():
        return
    if profile_path.stat().st_size == 0:
        logging.warning("perf profile %s is empty", profile_path)
        return
    if timeout_sec is None:
        timeout_sec = _perf_report_timeout_sec(profile_path)
    try:
        proc = subprocess.run(
            [
                perf,
                "report",
                "-i",
                str(profile_path),
                "--stdio",
                "--sort=symbol",
                "--no-children",
                "-g",
                "none",
                "--dsos",
                "simplifier",
                "-n",
                str(top_n),
                "--percent-limit",
                "0.5",
            ],
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
    except subprocess.TimeoutExpired:
        logging.warning(
            "perf report timed out after %.0fs for %s",
            timeout_sec,
            profile_path,
        )
        return
    if proc.returncode != 0:
        logging.warning(
            "perf report failed (%d): %s",
            proc.returncode,
            (proc.stderr or proc.stdout).strip()[:500],
        )
        return
    summary = _format_perf_report_summary(proc.stdout, top_n=top_n)
    if not summary:
        logging.warning(
            "perf profile summary for %s: no symbols (rebuild simplifier with debug info?)",
            profile_path,
        )
        return
    logging.warning(
        "perf profile summary for %s (top %d symbols in simplifier, --percent-limit 0.5):",
        profile_path,
        top_n,
    )
    for line in summary:
        logging.warning("  %s", line)


_DEFAULT_PERF_FREQ = 99
_PERF_CALL_GRAPH = "dwarf,1024"


def _perf_sample_freq() -> int:
    override = os.environ.get("RUST_PERF_FREQ")
    if override is None:
        return _DEFAULT_PERF_FREQ
    try:
        freq = int(override)
    except ValueError:
        logging.warning("RUST_PERF_FREQ=%r is not an integer; using %d", override, _DEFAULT_PERF_FREQ)
        return _DEFAULT_PERF_FREQ
    if freq <= 0:
        logging.warning("RUST_PERF_FREQ=%d must be positive; using %d", freq, _DEFAULT_PERF_FREQ)
        return _DEFAULT_PERF_FREQ
    return freq


def _wrap_with_perf(cmd: list[str], profile_path: Path) -> list[str] | None:
    perf = shutil.which("perf")
    if perf is None:
        logging.warning("perf not found; rust profiling skipped")
        return None
    profile_path.parent.mkdir(parents=True, exist_ok=True)
    freq = _perf_sample_freq()
    logging.warning(
        "perf record: -F %d -g %s (override: RUST_PERF_FREQ)",
        freq,
        _PERF_CALL_GRAPH,
    )
    return [
        perf,
        "record",
        "-F",
        str(freq),
        "-g",
        "--call-graph",
        _PERF_CALL_GRAPH,
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
    dump_steps_output: Path | None = None,
    dump_step_offset: int = 0,
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
    smt_in: bytes | None = None
    if not use_file_input:
        smt_in = _script_to_bytes(smt_script)
    dump_steps_enabled = getattr(ARGS(), "dump_steps", False) and (
        dump_steps_output or output_path
    ) is not None
    cmd = _build_simplifier_cmd(
        bin_path,
        rust_pipeline,
        timeout=timeout,
        input_path=str(input_path) if use_file_input else "-",
        output_path=str(output_path) if use_file_output else "-",
        dump_steps=dump_steps_enabled,
        dump_step_offset=dump_step_offset,
        dump_steps_output=dump_steps_output,
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
    # The rust domain_probe pass shells out to a solver by whatever
    # SIMPLIFIER_SOLVER names, defaulting to a bare "z3-nightly" it expects on
    # PATH. The workspace binaries are deliberately not on PATH, so hand it the
    # resolved path -- otherwise the pass silently finds nothing.
    _solver = solver_command(ARGS().solver, "rust simplifier")
    if _solver is not None:
        env["SIMPLIFIER_SOLVER"] = _solver
    env["LIFT_SUBSTITUTE"] = "1" if ARGS().lift_substitute else "0"
    # or_small only helps the `solver`/`memory` steps; elsewhere it just adds
    # branch cost and times z3 out. Gate it off outside those steps, unless
    # DEMOD_OR_SMALL is pinned explicitly.
    if "DEMOD_OR_SMALL" not in os.environ:
        _step = getattr(ARGS(), "optimization_step", None)
        if _step is None:
            _src = input_path if input_path is not None else getattr(ARGS(), "input", None)
            if _src is not None:
                _m = re.search(
                    r"_\d+_([a-z][a-z_]*)\.(?:soundness|completeness)", Path(_src).name
                )
                _step = _m.group(1) if _m else None
        if _step not in ("solver", "memory"):
            env["DEMOD_OR_SMALL"] = "1"
    proc = subprocess.run(
        cmd,
        input=smt_in,
        capture_output=True,
        text=smt_in is None,
        check=False,
        env=env,
    )
    if proc.returncode != 0:
        err = proc.stderr
        if isinstance(err, bytes):
            err = err.decode(SMT_ENCODING)
        raise RuntimeError(
            f"simplifier exited {proc.returncode}: {err.strip()}"
        )

    if profile_path is not None and profile_path.is_file():
        _last_rust_profile_path = profile_path
        logging.warning(
            "Rust profile data written to %s (view: verifier/flamegraph.py %s)",
            profile_path,
            profile_path,
        )
        emit_perf_profile_summary(profile_path)

    steps = parse_rust_stats(
        proc.stderr.decode(SMT_ENCODING)
        if isinstance(proc.stderr, bytes)
        else proc.stderr
    )
    if profile_path is not None and profile_path.is_file():
        _emit_rust_pass_timings(steps)

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
            if data.get("result") == "not-qf":
                logging.warning("formula is not quantifier-free")
            stats_dump("isqf", data)
        else:
            stats_dump(base, data)

    if not parse_output:
        return None, steps
    if use_file_output:
        with open(output_path, "rb") as out:
            return _bytes_to_script(out.read()), steps
    assert proc.stdout is not None
    return _bytes_to_script(proc.stdout), steps
