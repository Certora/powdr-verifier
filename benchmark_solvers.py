#!/usr/bin/env python3
import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark SMT solvers on SMT-LIB v2 files from configured directories."
    )
    parser.add_argument("config", type=Path, help="Path to benchmark configuration JSON file.")
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("benchmark-results.json"),
        help="Path to output result JSON file.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=5,
        help="Optional global timeout in seconds (overrides config timeout).",
    )
    return parser.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("Top-level configuration must be a JSON object.")
    return data

def run_solver(
    name: str,
    solver: list[str],
    smt_file: Path,
    timeout: float | None,
) -> dict[str, Any]:

    command = solver + [smt_file]

    started = time.perf_counter()

    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        duration = round(time.perf_counter() - started, 3)
        status = "ok" if completed.returncode == 0 else "error"
        return {
            "status": status,
            "return_code": completed.returncode,
            "duration_sec": duration,
            "stdout": completed.stdout.strip(),
            "stderr": completed.stderr.strip(),
        }
    except subprocess.TimeoutExpired as exc:
        duration = time.perf_counter() - started
        return {
            "status": "timeout",
            "return_code": None,
            "duration_sec": duration,
            "stdout": exc.stdout.strip() if isinstance(exc.stdout, str) else "",
            "stderr": exc.stderr.strip() if isinstance(exc.stderr, str) else "",
        }
    except OSError as exc:
        duration = time.perf_counter() - started
        return {
            "status": "spawn_error",
            "return_code": None,
            "duration_sec": duration,
            "stdout": "",
            "stderr": str(exc).strip(),
        }


def build_summary(results: list[dict[str, Any]]) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "total_runs": len(results),
        "ok": 0,
        "error": 0,
        "timeout": 0,
        "spawn_error": 0,
        "per_solver": {},
    }
    for result in results:
        status = result["status"]
        if status in ("ok", "error", "timeout", "spawn_error"):
            summary[status] += 1

        solver = result["solver"]
        if solver not in summary["per_solver"]:
            summary["per_solver"][solver] = {
                "ok": 0,
                "error": 0,
                "timeout": 0,
                "spawn_error": 0,
                "total": 0,
            }
        summary["per_solver"][solver]["total"] += 1
        if status in summary["per_solver"][solver]:
            summary["per_solver"][solver][status] += 1
    return summary


def main() -> int:
    args = parse_args()
    config_path = args.config.resolve()
    config = load_json(config_path)

    solvers = config["solvers"]

    directories = config.get("directories")
    if not isinstance(directories, list) or not directories:
        raise ValueError("Configuration must define a non-empty 'directories' array.")
    
    results = {}
    if args.output.exists():
        try:
            results = load_json(args.output)
        except:
            print("failed to load old results")
            pass

    try:
        for name, solver in solvers.items():
            for dir in directories:
                for smt_file in Path(dir).glob("*.rewrite.smt2"):
                    filestr = str(smt_file)
                    if filestr in results and name in results[filestr]:
                        print(f"skipping {name} on {smt_file} because it already exists")
                        continue
                    print(f"running {name} on {smt_file}")
                    result = run_solver(name, solver, smt_file, args.timeout)
                    if filestr not in results:
                        results[filestr] = {}
                    results[filestr][name] = result
    except KeyboardInterrupt:
        pass

    with args.output.open("w", encoding="utf-8") as f:
        json.dump(results, f, indent=4)

    print(f"Wrote benchmark results to: {args.output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as exc:
        print(f"Configuration error: {exc}", file=sys.stderr)
        raise SystemExit(2)
