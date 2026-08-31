#!/usr/bin/env python3
"""Download the sample powdr-dump tarball and verify one small pair from it.

A quick-start that does not build powdr.
"""
import json
import os
import shutil
import subprocess
import sys
import tarfile
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent
# pinned commit of https://github.com/alex-ozdemir/apc-examples, so the
# candidate ids below stay valid regardless of what's later added upstream
EXAMPLES_COMMIT = "ea27130ee102b9a6980821e0de218cd38ae77c17"
URL = f"https://github.com/alex-ozdemir/apc-examples/archive/{EXAMPLES_COMMIT}.tar.gz"
VENV_DIR = REPO_ROOT / ".venv"
DOWNLOAD_DIR = REPO_ROOT / "powdr-dumps" / "_sample-download"

SCENARIO_DIR = "reth-selection"
BASE_DUMP = "apc_candidate_2702740_000_unopt.json"
SUBSTITUTIONS = "apc_candidate_2702740_substitutions.json"
BEFORE = "apc_candidate_2702740_026_rule_based.json"
AFTER = "apc_candidate_2702740_027_range_constraints.json"
PASSNAME = "range_constraints"


def venv_python() -> Path:
    return VENV_DIR / ("Scripts/python.exe" if os.name == "nt" else "bin/python3")


def ensure_venv() -> Path:
    py = venv_python()
    if not py.exists():
        subprocess.run([sys.executable, "-m", "venv", str(VENV_DIR)], check=True)
    subprocess.run(
        [str(py), "-m", "pip", "install", "-q",
         "-r", str(REPO_ROOT / "requirements.txt"), "z3-solver"],
        check=True,
    )
    return py


def ensure_solver() -> None:
    system_z3 = shutil.which("z3")
    if not system_z3:
        sys.exit("no system 'z3' found on PATH; install z3 and re-run")
    # pysmt's solver registry hardcodes these two paths and crashes at import
    # time if either is missing; point both at the system z3.
    for name in ("z3-nightly", "z3-4.16.0"):
        target = Path(f"~/bin/{name}").expanduser()
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(system_z3)


def download_and_extract() -> Path:
    extract_dir = DOWNLOAD_DIR / "extracted"
    if not any(extract_dir.glob("**/apc_candidate_*.json")):
        DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
        archive = DOWNLOAD_DIR / "examples.tar.gz"
        urllib.request.urlretrieve(URL, archive)

        extract_dir.mkdir(parents=True, exist_ok=True)
        with tarfile.open(archive) as tf:
            tf.extractall(extract_dir, filter="data")

    # the archive wraps everything in a single "apc-examples-<commit>" directory
    return next(extract_dir.glob(f"**/{SCENARIO_DIR}"))


def run_main(py: Path, *args: str) -> str:
    """Run `main.py *args`, suppressing its log noise; return stdout, or exit on failure."""
    proc = subprocess.run([str(py), "main.py", *args], cwd=REPO_ROOT, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(proc.stderr)
    return proc.stdout


def main() -> None:
    print("== setting up venv ==\n")
    py = ensure_venv()
    ensure_solver()

    print("\n== downloading sample powdr dump ==\n")
    extract_dir = download_and_extract()
    before, after = extract_dir / BEFORE, extract_dir / AFTER
    base_dump, substitutions = extract_dir / BASE_DUMP, extract_dir / SUBSTITUTIONS

    print(
        "\n== verifying pair ==\n\n"
        f"  before        = {before}\n"
        f"  after         = {after}\n"
        f"  pass          = {PASSNAME}\n"
        f"  base_dump     = {base_dump}\n"
        f"  substitutions = {substitutions}\n"
    )

    out = DOWNLOAD_DIR / "out.smt2"
    # --base-dump/--substitutions must come before "verify"
    run_main(
        py,
        "--base-dump", str(base_dump),
        "--substitutions", str(substitutions),
        "verify", str(before), str(after), str(out),
        "--optimization-step", PASSNAME,
    )

    for kind in ("soundness", "completeness"):
        smt2 = out.with_suffix(f".{kind}.smt2")
        if not smt2.exists():
            continue
        rewritten = smt2.with_suffix(".rewrite.smt2")
        run_main(py, "simplify", str(smt2), "default", str(rewritten), "--optimization-step", PASSNAME)
        print(f"== {kind} ==\n")
        print(json.dumps(json.loads(run_main(py, "check", str(rewritten))), indent=2))
        print()


if __name__ == "__main__":
    main()
