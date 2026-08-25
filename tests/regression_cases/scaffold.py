#!/usr/bin/env python3
"""Scaffold a new regression case from benchmark artifacts."""

from __future__ import annotations

import argparse
import fnmatch
import shutil
import sys
from pathlib import Path

VERIFIER_DIR = Path(__file__).resolve().parents[2]
CASES_ROOT = VERIFIER_DIR / "tests" / "regression_cases"

TEMPLATES: dict[str, str] = {
    "simplify-pass": '''[case]
tags = [{tags}]
description = """
TODO: what this regression guards.
"""

[inputs]
smt = "{smt_file}"

[[steps]]
script = "main.py"
args = ["simplify", "{{smt}}", "PASS_NAME", "{{work}}/out.smt2"]
timeout = 60
capture_json = true

[[assert]]
kind = "exit_ok"

[[assert]]
kind = "pass_stats"
pass = "PASS_NAME"
field = "asserts_changed"
min = 1
''',
    "verify-pipeline": '''[case]
tags = [{tags}]
description = """
TODO: verify → simplify → check pipeline regression.
"""

[source]
dataset = "DATASET"
block = "BLOCK_ID"
powdr_commit = "POWDR_COMMIT"
base = "unopt"
before = "BEFORE_PASS"
after = "AFTER_PASS"
substitutions = true

[inputs]
base = "BASE.json"
substitutions = "SUBSTITUTIONS.json"
before = "BEFORE.json"
after = "AFTER.json"
check = "soundness"

[[steps]]
script = "main.py"
args = [
  "--base-dump", "{{base}}",
  "--substitutions", "{{substitutions}}",
  "verify", "{{before}}", "{{after}}", "{{work}}/vc",
]
timeout = 120

[[steps]]
script = "main.py"
args = [
  "simplify",
  "{{work}}/vc.{{check}}.smt2",
  "nnf:skolem:lift:witness:z3-propagate-values:isqf:bounds:rewrite:bitwise:mod_inv:demod:domain_probe:pretty",
  "{{work}}/vc.{{check}}.rewrite.smt2",
]
timeout = 120
capture_json = true

[[steps]]
script = "main.py"
args = ["check", "{{work}}/vc.{{check}}.rewrite.smt2"]
timeout = 60
capture_json = true

[[assert]]
kind = "exit_ok"

[[assert]]
kind = "check_result"
result = "unsat"
''',
    "orchestrate-verify": '''[case]
tags = [{tags}]
description = """
TODO: orchestrate verify step on staged dumps.
"""

[inputs]
type = "dumps"
dataset = "regression-CASE_NAME"
# copy apc_candidate_*.json into this directory

[[steps]]
script = "orchestrate.py"
args = ["verify", "{{dataset}}", "BLOCK:STEP"]
timeout = 300
''',
}


def _copy_files(src_dir: Path, dst_dir: Path, patterns: list[str]) -> list[str]:
    copied: list[str] = []
    for path in sorted(src_dir.iterdir()):
        if not path.is_file():
            continue
        if not any(fnmatch.fnmatch(path.name, pat) for pat in patterns):
            continue
        shutil.copy2(path, dst_dir / path.name)
        copied.append(path.name)
    return copied


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True, help="Case directory name")
    parser.add_argument("--tags", required=True, help="Comma-separated tags")
    parser.add_argument("--from", dest="src", required=True, type=Path, help="Source directory")
    parser.add_argument(
        "--files",
        default="*",
        help="Glob pattern(s) for files to copy (comma-separated)",
    )
    parser.add_argument(
        "--template",
        choices=sorted(TEMPLATES),
        default="simplify-pass",
        help="case.toml template",
    )
    parser.add_argument("--smt-file", help="Input smt2 filename for simplify-pass template")
    args = parser.parse_args(argv)

    dst = CASES_ROOT / args.name
    if dst.exists():
        print(f"error: {dst} already exists", file=sys.stderr)
        return 1

    dst.mkdir(parents=True)
    patterns = [p.strip() for p in args.files.split(",")]
    copied = _copy_files(args.src, dst, patterns)
    if not copied:
        print(f"warning: no files copied from {args.src} matching {patterns}", file=sys.stderr)

    tags = ", ".join(f'"{t.strip()}"' for t in args.tags.split(",") if t.strip())
    body = TEMPLATES[args.template].format(
        tags=tags,
        smt_file=args.smt_file or (copied[0] if copied else "input.smt2"),
    )
    body = body.replace("CASE_NAME", args.name)
    (dst / "case.toml").write_text(body)

    print(f"created {dst}")
    print(f"copied: {', '.join(copied) or '(none)'}")
    print("edit case.toml: fill description, steps, and asserts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
