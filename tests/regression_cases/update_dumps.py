#!/usr/bin/env python3
"""Refresh committed regression dumps from verifier/powdr-dumps/."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

_VERIFIER_DIR = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_VERIFIER_DIR))
_REG = importlib.util.spec_from_file_location("_reg", _VERIFIER_DIR / "tests" / "regressions.py")
_mod = importlib.util.module_from_spec(_REG)
assert _REG.loader
_REG.loader.exec_module(_mod)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("cases", nargs="*", help="default: all cases with [source]")
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args(argv)
    names = args.cases or [c.name for c in _mod.discover_cases() if c.source]
    if not names:
        print("no cases to update", file=sys.stderr)
        return 1
    failed = 0
    for name in names:
        try:
            r = _mod.update_case_dumps(name, dry_run=args.dry_run)
            print(f"{'would update' if args.dry_run else 'updated'} {name}: {r}")
        except Exception as exc:
            failed += 1
            print(f"error: {name}: {exc}", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
