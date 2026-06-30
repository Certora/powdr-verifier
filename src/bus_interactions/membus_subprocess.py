"""Subprocess client for ``membus.py extract --json`` (match-var preanalysis)."""
from __future__ import annotations

import json
import logging
import subprocess
from functools import lru_cache
from pathlib import Path

_LOG = logging.getLogger(__name__)

_MEMBUS_SCRIPT = Path(__file__).resolve().parents[2] / "membus.py"


@lru_cache(maxsize=8)
def _fetch_extract_json_cached(path_str: str, mtime_ns: int) -> dict | None:
    del mtime_ns
    path = Path(path_str)
    try:
        proc = subprocess.run(
            [_MEMBUS_SCRIPT, "extract", "--json", "--file-a", str(path)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as e:
        _LOG.warning("membus extract subprocess failed for %s: %s", path, e)
        return None
    if proc.returncode != 0:
        _LOG.warning(
            "membus extract exited %d for %s: %s",
            proc.returncode,
            path,
            proc.stderr.strip() or proc.stdout.strip(),
        )
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        _LOG.warning("membus extract JSON parse failed for %s: %s", path, e)
        return None


def fetch_extract_json(dump_path: Path | None) -> dict | None:
    """Run ``membus extract --json`` on ``dump_path``; ``None`` if unavailable."""
    if dump_path is None or not dump_path.is_file():
        return None
    try:
        mtime_ns = dump_path.stat().st_mtime_ns
    except OSError as e:
        _LOG.warning("membus extract cannot stat %s: %s", dump_path, e)
        return None
    return _fetch_extract_json_cached(str(dump_path.resolve()), mtime_ns)
