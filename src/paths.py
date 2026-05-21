"""Workspace layout: verifier root, powdr sibling, and standard data/report dirs.

Helpers create dump and data subdirectories used by tests and batch runs.
"""
from pathlib import Path

VERIFIER_DIR = Path(__file__).resolve().parent.parent
WORKSPACE_DIR = VERIFIER_DIR.parent
POWDR_DIR = WORKSPACE_DIR / "powdr"
POWDR_DUMPS_DIR = VERIFIER_DIR / "powdr-dumps"
DATA_DIR = VERIFIER_DIR / "data"
REPORTS_DIR = VERIFIER_DIR / "reports"


def ensure_layout() -> None:
    for directory in (POWDR_DUMPS_DIR, DATA_DIR, REPORTS_DIR):
        directory.mkdir(parents=True, exist_ok=True)


def dump_dir(test: str) -> Path:
    path = POWDR_DUMPS_DIR / test
    path.mkdir(parents=True, exist_ok=True)
    return path


def data_dir(test: str) -> Path:
    path = DATA_DIR / test
    path.mkdir(parents=True, exist_ok=True)
    return path


def data_path_for_dump(dump: Path, name: str) -> Path:
    rel = dump.relative_to(POWDR_DUMPS_DIR)
    out = DATA_DIR / rel.parent / name
    out.parent.mkdir(parents=True, exist_ok=True)
    return out
