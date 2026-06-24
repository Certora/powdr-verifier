"""Workspace layout: verifier root, powdr sibling, and standard data/report dirs.

Helpers create dump and data subdirectories used by tests and batch runs.
"""
import shlex
import shutil
import sys
from pathlib import Path

from src.utils.args import ARGS

VERIFIER_DIR = Path(__file__).resolve().parent.parent
WORKSPACE_DIR = VERIFIER_DIR.parent
POWDR_DIR = WORKSPACE_DIR / "powdr"
POWDR_DUMPS_DIR = VERIFIER_DIR / "powdr-dumps"
DATA_DIR = VERIFIER_DIR / "data"
REPORTS_DIR = VERIFIER_DIR / "reports"

_REL_VERIFIER = VERIFIER_DIR.relative_to(WORKSPACE_DIR).as_posix()
MAIN_SCRIPT = f"./{_REL_VERIFIER}/main.py"
ORCHESTRATE_SCRIPT = f"./{_REL_VERIFIER}/orchestrate.py"
_PRLIMIT_BIN = shutil.which("prlimit")


def arg_for_dump(arg) -> str:
    path = Path(arg)
    if path.is_absolute():
        try:
            return f"./{path.relative_to(WORKSPACE_DIR).as_posix()}"
        except ValueError:
            pass
    return str(arg)


def dump_cmd_parts(parts: list) -> str:
    out: list[str] = []
    i = 0
    while i < len(parts):
        s = str(parts[i])
        if _PRLIMIT_BIN and s == _PRLIMIT_BIN:
            i += 2
            continue
        if s == sys.executable or Path(s).name in ("python", "python3"):
            if i + 1 < len(parts) and Path(str(parts[i + 1])).name in ("main.py", "orchestrate.py"):
                script = (
                    MAIN_SCRIPT
                    if Path(str(parts[i + 1])).name == "main.py"
                    else ORCHESTRATE_SCRIPT
                )
                out.append(script)
                i += 2
                continue
        if Path(s).name == "main.py":
            out.append(MAIN_SCRIPT)
            i += 1
            continue
        if Path(s).name == "orchestrate.py":
            out.append(ORCHESTRATE_SCRIPT)
            i += 1
            continue
        out.append(arg_for_dump(parts[i]))
        i += 1
    return shlex.join(out)


def ensure_layout() -> None:
    for directory in (POWDR_DUMPS_DIR, DATA_DIR, REPORTS_DIR):
        directory.mkdir(parents=True, exist_ok=True)


def dump_dir(test: str) -> Path:
    path = POWDR_DUMPS_DIR / test
    path.mkdir(parents=True, exist_ok=True)
    return path


def data_dir(test: str) -> Path:
    path = DATA_DIR / f"{test}{ARGS().run_id}"
    path.mkdir(parents=True, exist_ok=True)
    return path


def data_path_for_dump(dump: Path, name: str) -> Path:
    rel = dump.relative_to(POWDR_DUMPS_DIR)
    key = f"{rel.parent.as_posix()}{ARGS().run_id}"
    out = DATA_DIR / key / name
    out.parent.mkdir(parents=True, exist_ok=True)
    return out
