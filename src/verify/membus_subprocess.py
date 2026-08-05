"""Subprocess client for ``membus.py`` JSON subcommands."""
from __future__ import annotations

import copy
import json
import logging
import subprocess
import sys
from pathlib import Path

_LOG = logging.getLogger(__name__)

_MEMBUS_SCRIPT = Path(__file__).resolve().parents[2] / "membus.py"

# Per-process memo of ``membus.py`` results, keyed on the exact argv.
#
# Every subcommand is a pure function of the (immutable, during one verify)
# input dump file(s) plus its flags, so identical argv => identical output.
# An is_valid-gated pass runs the membus analysis TWICE (completeness with
# after_assume_is_valid=True, then the is_valid special-soundness round with
# =False); the before-side calls (align/info/extract/solve) and the after-side
# align/info/extract are byte-identical across both rounds. Caching them avoids
# recomputing the expensive before-side symbolic (address-space-2) solve — ~11 s
# on the guest-keccak ``040`` blocks — a second time. Only the after-side
# ``solve`` differs (its ``--assume-is-valid`` flag), so it is not deduped.
_MEMBUS_JSON_CACHE: dict[tuple[str, ...], dict | None] = {}


def reset_membus_cache() -> None:
    """Drop the per-process membus result cache. Called at the start of each
    ``verify`` so the cache is scoped to one before/after pair (the two is_valid
    rounds); keeps the key (argv, which names the input files) from ever going
    stale if a single process reuses a path with different content."""
    _MEMBUS_JSON_CACHE.clear()


def _run_membus_json(args: list[str]) -> dict | None:
    key = tuple(args)
    if key in _MEMBUS_JSON_CACHE:
        cached = _MEMBUS_JSON_CACHE[key]
        # Return a copy: callers may mutate the result while building their side.
        return copy.deepcopy(cached) if cached is not None else None
    result = _run_membus_json_uncached(args)
    _MEMBUS_JSON_CACHE[key] = result
    return copy.deepcopy(result) if result is not None else None


def _run_membus_json_uncached(args: list[str]) -> dict | None:
    try:
        proc = subprocess.run(
            # Run under *this* interpreter, not membus.py's `python3` shebang:
            # the shebang picks up whatever python3 is on PATH, which misses the
            # verifier venv (and its z3) unless the venv is activated.
            [sys.executable, str(_MEMBUS_SCRIPT), *args],
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


def fetch_solve_json(
    dump_path: Path | None,
    *,
    addr_space: int = 1,
    assume_is_valid: bool = False,
) -> dict | None:
    if dump_path is None or not dump_path.is_file():
        return None
    args = ["solve", "--json", "--file-a", str(dump_path), "--as", str(addr_space)]
    if assume_is_valid:
        args.insert(1, "--assume-is-valid")
    else:
        args.insert(1, "--no-assume-is-valid")
    return _run_membus_json(args)


def fetch_solve_json_all(
    dump_path: Path | None,
    *,
    present: set[int] | None = None,
    addr_spaces: tuple[int, ...] = (1, 2),
    assume_is_valid: bool = False,
) -> dict | None:
    """Run ``solve`` for each address space and merge interaction rows."""
    if dump_path is None or not dump_path.is_file():
        return None
    merged: dict | None = None
    for addr_space in addr_spaces:
        if present is not None and addr_space not in present:
            continue
        sol = fetch_solve_json(
            dump_path, addr_space=addr_space, assume_is_valid=assume_is_valid
        )
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
