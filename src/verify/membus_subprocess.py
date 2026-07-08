"""Subprocess client for ``membus.py`` JSON subcommands."""
from __future__ import annotations

import json
import logging
import subprocess
from pathlib import Path

_LOG = logging.getLogger(__name__)

_MEMBUS_SCRIPT = Path(__file__).resolve().parents[2] / "membus.py"


def _run_membus_json(args: list[str]) -> dict | None:
    try:
        proc = subprocess.run(
            [_MEMBUS_SCRIPT, *args],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as e:
        _LOG.warning("membus %s failed: %s", args[:1], e)
        return None
    if proc.returncode != 0:
        _LOG.warning(
            "membus %s exited %d: %s",
            args[:1],
            proc.returncode,
            proc.stderr.strip() or proc.stdout.strip(),
        )
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        _LOG.warning("membus %s JSON parse failed: %s", args[:1], e)
        return None


def fetch_solve_json(dump_path: Path | None, *, addr_space: int = 1) -> dict | None:
    if dump_path is None or not dump_path.is_file():
        return None
    return _run_membus_json(
        ["solve", "--json", "--file-a", str(dump_path), "--as", str(addr_space)]
    )


def fetch_solve_json_all(
    dump_path: Path | None,
    *,
    present: set[int] | None = None,
    addr_spaces: tuple[int, ...] = (1, 2),
) -> dict | None:
    """Run ``solve`` for each address space and merge interaction rows."""
    if dump_path is None or not dump_path.is_file():
        return None
    merged: dict | None = None
    for addr_space in addr_spaces:
        if present is not None and addr_space not in present:
            continue
        sol = fetch_solve_json(dump_path, addr_space=addr_space)
        if sol is None:
            continue
        if merged is None:
            merged = sol
        else:
            merged = {
                **merged,
                "interactions": (merged.get("interactions") or [])
                + (sol.get("interactions") or []),
            }
    return merged


def fetch_extract_json(dump_path: Path | None) -> dict | None:
    if dump_path is None or not dump_path.is_file():
        return None
    return _run_membus_json(["extract", "--json", "--file-a", str(dump_path)])


def fetch_info_json(
    dump_path: Path | None, *, addr_space: int | None = None
) -> dict | None:
    if dump_path is None or not dump_path.is_file():
        return None
    args = ["info", "--json", "--file-a", str(dump_path)]
    if addr_space is not None:
        args.extend(["--as", str(addr_space)])
    return _run_membus_json(args)


def fetch_align_json(
    before_path: Path | None,
    after_path: Path | None,
    *,
    addr_space: int,
) -> dict | None:
    if before_path is None or not before_path.is_file():
        return None
    if after_path is None or not after_path.is_file():
        return None
    return _run_membus_json(
        [
            "align",
            "--json",
            "--file-a",
            str(before_path),
            "--file-b",
            str(after_path),
            "--as",
            str(addr_space),
        ]
    )
