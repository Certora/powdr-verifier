"""Subprocess integration with the Rust ``checker`` binary."""
import json
import logging
import os
import subprocess
from pathlib import Path

from ..utils.args import ARGS


def _verifier_root() -> Path:
    return Path(__file__).resolve().parents[2]


def resolve_checker_bin() -> Path | None:
    override = os.environ.get("CHECKER_BIN")
    if override:
        path = Path(override).expanduser()
        if path.is_file():
            return path
        logging.warning("CHECKER_BIN=%s does not exist", override)
    rust_dir = _verifier_root() / "rust"
    for profile in ("release", "debug"):
        candidate = rust_dir / "target" / profile / "checker"
        if candidate.is_file():
            return candidate
    return None


def _build_checker_cmd(
    bin_path: Path,
    input_path: str,
    *,
    dump_model: Path | None = None,
    solve_chunked: bool | None = None,
    timeout: float | None = None,
) -> list[str]:
    cmd = [str(bin_path)]
    if dump_model is not None:
        cmd.extend(["--dump-model", str(dump_model)])
    if timeout is not None:
        cmd.extend(["--timeout", str(timeout)])
    chunked = (
        solve_chunked
        if solve_chunked is not None
        else getattr(ARGS(), "solve_chunked", True)
    )
    cmd.append("--solve-chunked" if chunked else "--no-solve-chunked")
    cmd.append(input_path)
    return cmd


def run_checker_subprocess(
    input_path: Path | str,
    *,
    dump_model: Path | None = None,
    solve_chunked: bool | None = None,
    check_timeout: float | None = None,
) -> dict:
    bin_path = resolve_checker_bin()
    if bin_path is None:
        raise FileNotFoundError("checker binary not found")
    cmd = _build_checker_cmd(
        bin_path,
        str(input_path),
        dump_model=dump_model or getattr(ARGS(), "dump_model", None),
        solve_chunked=solve_chunked,
        timeout=check_timeout,
    )
    proc = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"checker exited {proc.returncode}: {proc.stderr.strip()}"
        )
    data = json.loads(proc.stdout)
    if isinstance(data, dict) and "__Action" in data:
        return data["__Action"]
    return data


def run_checker_subprocess_text(
    smt_text: str,
    *,
    dump_model: Path | None = None,
    solve_chunked: bool | None = None,
    check_timeout: float | None = None,
) -> dict:
    bin_path = resolve_checker_bin()
    if bin_path is None:
        raise FileNotFoundError("checker binary not found")
    cmd = _build_checker_cmd(
        bin_path,
        "-",
        dump_model=dump_model,
        solve_chunked=solve_chunked,
        timeout=check_timeout,
    )
    proc = subprocess.run(
        cmd,
        input=smt_text,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"checker exited {proc.returncode}: {proc.stderr.strip()}"
        )
    data = json.loads(proc.stdout)
    if isinstance(data, dict) and "__Action" in data:
        return data["__Action"]
    return data


def merge_solve_action(python_action, rust_data: dict) -> str:
    """Copy solve attempts/result from a Rust checker action into ``python_action``."""
    solve = next(
        (a for a in rust_data.get("actions", []) if a.get("name") == "solve"),
        rust_data,
    )
    for child in solve.get("actions", []):
        python_action += action_from_dict(child)
    res = solve.get("result") or rust_data.get("result") or "unknown"
    if res == "sat":
        model = solve.get("model")
        if model is not None:
            python_action += {"model": model}
        dump_model = getattr(ARGS(), "dump_model", None)
        if dump_model:
            logging.info("dumping model to %s", dump_model)
            with open(dump_model, "w") as f:
                json.dump(model or {}, f, indent=4)
    if python_action.expected is not None:
        from ..report.action import classify_expected_vs_result

        o = classify_expected_vs_result(
            name=python_action.name, expected=python_action.expected, result=res
        )
        if o == "wrong":
            logging.error("expected %s but got %s", python_action.expected, res)
        elif o == "timeout":
            logging.warning(
                "expected %s; solver timed out (result %s)",
                python_action.expected,
                res,
            )
        elif o != "success":
            logging.error("expected %s but got %s", python_action.expected, res)
    python_action += {"result": res}
    return res


def action_from_dict(data: dict):
    from ..report.action import Action

    actions = [action_from_dict(a) for a in data.get("actions", [])]
    props = {
        k: v
        for k, v in data.items()
        if k not in ("actions", "enter_time", "exit_time", "running_time", "name")
    }
    return Action(
        data.get("name", "check"),
        enter_time=data.get("enter_time"),
        exit_time=data.get("exit_time"),
        running_time=data.get("running_time"),
        actions=actions,
        **props,
    )
