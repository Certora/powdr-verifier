"""Subprocess integration with the Rust ``checker`` binary."""
import json
import logging
import os
import subprocess
import sys
from pathlib import Path

from ..utils.args import ARGS
from ..utils.process import communicate_with_timeout


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
    chunked = solve_chunked if solve_chunked is not None else True
    cmd.append("--solve-chunked" if chunked else "--no-solve-chunked")
    cmd.append(input_path)
    return cmd


def _emit_stderr(stderr: str | None) -> None:
    if stderr:
        sys.stderr.write(stderr)
        if not stderr.endswith("\n"):
            sys.stderr.write("\n")
        sys.stderr.flush()


def _effective_check_timeout(check_timeout: float | None) -> float | None:
    if check_timeout is not None:
        return check_timeout
    return getattr(ARGS(), "timeout", None)


def _timeout_action() -> dict:
    return {"name": "check", "result": "timeout"}


def _run_checker_proc(
    cmd: list[str],
    *,
    stdin: str | None = None,
    check_timeout: float | None = None,
) -> dict:
    timeout = _effective_check_timeout(check_timeout)
    if timeout is not None:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE if stdin is not None else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if stdin is not None and proc.stdin is not None:
            proc.stdin.write(stdin)
            proc.stdin.close()
        stdout, stderr, timed_out = communicate_with_timeout(proc, timeout)
        _emit_stderr(stderr)
        if timed_out:
            logging.warning("checker subprocess timed out after %.1fs", timeout)
            return _timeout_action()
        if proc.returncode != 0:
            raise RuntimeError(
                f"checker exited {proc.returncode}: {(stderr or '').strip()}"
            )
        data = json.loads(stdout or "")
    else:
        proc = subprocess.run(
            cmd,
            input=stdin,
            capture_output=True,
            text=True,
            check=False,
        )
        _emit_stderr(proc.stderr)
        if proc.returncode != 0:
            raise RuntimeError(
                f"checker exited {proc.returncode}: {proc.stderr.strip()}"
            )
        data = json.loads(proc.stdout)
    if isinstance(data, dict) and "__Action" in data:
        return data["__Action"]
    return data


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
    timeout = _effective_check_timeout(check_timeout)
    cmd = _build_checker_cmd(
        bin_path,
        str(input_path),
        dump_model=dump_model or getattr(ARGS(), "dump_model", None),
        solve_chunked=solve_chunked,
        timeout=timeout,
    )
    return _run_checker_proc(cmd, check_timeout=timeout)


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
