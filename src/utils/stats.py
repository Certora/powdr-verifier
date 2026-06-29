"""Opt-in JSON stats dumps under ``data/<test>/stats/<run-id>/``."""
from __future__ import annotations

import functools
import re
import shutil
import time
from pathlib import Path
from typing import Any, Callable, TypeVar

from ..paths import DATA_DIR, POWDR_DUMPS_DIR
from .args import ARGS
from .inputs import parse_filename
from .io import dump_json

_F = TypeVar("_F", bound=Callable[..., Any])

_stats_dir: Path | None = None
_current_tag: str | None = None
_current_pass_action: Any = None

_OBLIGATION_RE = re.compile(r"\.(?P<tag>completeness|soundness)(?:\.|$)")


def stats_enabled() -> bool:
    return getattr(ARGS(), "stats_run_id", None) is not None


def verify_run_id(before: Path, after: Path) -> str:
    parsed_before = parse_filename(before)
    parsed_after = parse_filename(after)
    if parsed_before is None or parsed_after is None:
        raise ValueError(f"cannot derive stats run id from {before} and {after}")
    block_a, step_a, _ = parsed_before
    block_b, step_b, _ = parsed_after
    if block_a != block_b:
        raise ValueError(f"block mismatch for stats run id: {before} vs {after}")
    return f"verify-{block_a}-{step_a:03d}-{step_b:03d}"


def stats_test_from_path(path: Path) -> str:
    resolved = path.resolve()
    for base in (POWDR_DUMPS_DIR, DATA_DIR):
        try:
            rel = resolved.relative_to(base.resolve())
            return rel.parts[0]
        except ValueError:
            continue
    raise ValueError(f"cannot derive stats test name from {path}")


def stats_dir_for_run(test: str, run_id: str) -> Path:
    return DATA_DIR / test / "stats" / run_id


def stats_tag_from_path(path: Path) -> str:
    stem = path.name
    if stem.endswith(".smt2"):
        stem = stem[: -len(".smt2")]
    if stem.endswith(".rewrite"):
        stem = stem[: -len(".rewrite")]
    if stem.endswith(".model"):
        stem = stem[: -len(".model")]
    if m := _OBLIGATION_RE.search(stem):
        return m.group("tag")
    if stem.startswith("verify-"):
        return "encode"
    return "unknown"


def _sanitize_segment(value: str) -> str:
    return re.sub(r"[\s/]+", "-", value)


def _resolve_run_id(run_id: str | None) -> str:
    if run_id:
        return run_id
    arg = getattr(ARGS(), "stats_run_id", None)
    if arg is not None:
        return arg
    raise ValueError("stats run id not provided")


def _current_stats_tag(*, tag: str | None = None) -> str:
    if tag is not None:
        return tag
    if _current_tag is not None:
        return _current_tag
    stats_tag = getattr(ARGS(), "stats_tag", None)
    if stats_tag is not None:
        return stats_tag
    command = ARGS().command
    if command == "verify":
        return "encode"
    if command in ("simplify", "check") and hasattr(ARGS(), "input"):
        return stats_tag_from_path(ARGS().input)
    return "unknown"


def prepare_stats_dir(test: str, run_id: str, *, wipe: bool = True) -> Path:
    stats_dir = stats_dir_for_run(test, run_id)
    if wipe and stats_dir.exists():
        shutil.rmtree(stats_dir)
    stats_dir.mkdir(parents=True, exist_ok=True)
    return stats_dir


def init_stats_run(
    *,
    run_id: str | None = None,
    test: str | None = None,
    tag: str | None = None,
    wipe: bool = True,
) -> Path | None:
    global _stats_dir
    if not stats_enabled():
        return None
    resolved_id = _resolve_run_id(run_id)
    if test is None:
        command = ARGS().command
        if command == "verify":
            test = stats_test_from_path(ARGS().input_before)
        elif command in ("simplify", "check", "aliasing", "text"):
            test = stats_test_from_path(ARGS().input)
        else:
            raise ValueError(f"cannot derive stats test for command {command}")
    stats_dir = prepare_stats_dir(test, resolved_id, wipe=wipe)
    _stats_dir = stats_dir
    if tag is not None:
        set_stats_tag(tag)
    return stats_dir


def set_stats_tag(tag: str) -> None:
    global _current_tag
    _current_tag = tag


def set_pass_action(action: Any) -> Any:
    """Attach ``stats_dump`` payloads to the active simplifier pass ``Action``."""
    global _current_pass_action
    prev = _current_pass_action
    _current_pass_action = action
    return prev


def clear_pass_action(token: Any) -> None:
    global _current_pass_action
    _current_pass_action = token


def stats_dump(name: str, data: Any, *, tag: str | None = None) -> Path | None:
    global _current_pass_action
    if isinstance(data, dict) and _current_pass_action is not None:
        _current_pass_action += data
    if not stats_enabled() or _stats_dir is None:
        return None
    t_ns = time.time_ns()
    resolved_tag = _current_stats_tag(tag=tag)
    filename = f"{t_ns}-{_sanitize_segment(resolved_tag)}-{_sanitize_segment(name)}.json"
    path = _stats_dir / filename
    if isinstance(data, dict):
        payload: dict[str, Any] = {"t_ns": t_ns, "tag": resolved_tag, **data}
    else:
        payload = {"t_ns": t_ns, "tag": resolved_tag, "data": data}
    with open(path, "w", encoding="utf-8") as f:
        dump_json(payload, f, indent=2)
    return path


def _write_profile(path: Path, payload: dict[str, Any]) -> None:
    with open(path, "w", encoding="utf-8") as f:
        dump_json(payload, f, indent=2)


def profile(name_or_fn: str | _F | None = None) -> _F | Callable[[_F], _F]:
    def decorate(fn: _F, *, name: str | None = None) -> _F:
        profile_name = name or fn.__name__

        @functools.wraps(fn)
        def wrapped(*args, **kwargs):
            if not stats_enabled() or _stats_dir is None:
                return fn(*args, **kwargs)
            t_start_ns = time.time_ns()
            resolved_tag = _current_stats_tag()
            filename = (
                f"{t_start_ns}-{_sanitize_segment(resolved_tag)}-"
                f"profile-{_sanitize_segment(profile_name)}.json"
            )
            path = _stats_dir / filename
            payload: dict[str, Any] = {
                "t_ns": t_start_ns,
                "tag": resolved_tag,
                "name": profile_name,
                "function": fn.__qualname__,
            }
            _write_profile(path, payload)
            try:
                return fn(*args, **kwargs)
            finally:
                payload["t_end_ns"] = time.time_ns()
                _write_profile(path, payload)

        return wrapped  # type: ignore[return-value]

    if callable(name_or_fn):
        return decorate(name_or_fn)
    return lambda fn: decorate(fn, name=name_or_fn)
