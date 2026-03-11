#!/usr/bin/env python3
import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot benchmark results in one figure grouped by solver and parent folder."
    )
    parser.add_argument(
        "input",
        type=Path,
        default=Path("benchmark-results.json"),
        help="Path to benchmark results JSON.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("benchmark-plots/all-solvers.png"),
        help="Path to output plot image.",
    )
    parser.add_argument(
        "--show",
        action="store_true",
        help="Show plots interactively in addition to saving them.",
    )
    parser.add_argument(
        "--solvers",
        nargs="+",
        default=None,
        help="Optional list of solver names to include in the plot.",
    )
    return parser.parse_args()


def load_results(path: Path) -> dict[str, dict[str, dict[str, Any]]]:
    with path.open("r", encoding="utf-8") as f:
        raw = json.load(f)
    if not isinstance(raw, dict):
        raise ValueError("Top-level benchmark result must be a JSON object.")
    return raw


def extract_y_value(run_result: dict[str, Any]) -> float:
    # Prefer explicit timeout field if present; otherwise use measured runtime.
    if "timeout_sec" in run_result:
        return float(run_result["timeout_sec"])
    if "duration_sec" in run_result:
        return float(run_result["duration_sec"])
    raise ValueError("Run result must contain either 'timeout_sec' or 'duration_sec'.")


def rewrite_filename_label(filename: str) -> str:
    index_match = re.search(r"apc_candidate_0_(\d+)", filename)
    index = index_match.group(1) if index_match else "unknown"

    if ".soundness." in filename:
        kind = "soundness"
    elif ".completeness." in filename:
        kind = "completeness"
    else:
        kind = "unknown"

    return f"{index}_{kind}"


def collect_series(
    results: dict[str, dict[str, dict[str, Any]]]
) -> dict[str, list[tuple[str, float]]]:
    # "solver | folder" -> [(filename, y_value), ...]
    grouped: dict[str, list[tuple[str, float]]] = defaultdict(list)

    for input_file, per_solver in results.items():
        input_path = Path(input_file)
        folder = input_path.parent.name if input_path.parent.name else str(input_path.parent)
        filename = rewrite_filename_label(input_path.name)

        if not isinstance(per_solver, dict):
            continue

        for solver_name, run_result in per_solver.items():
            if not isinstance(run_result, dict):
                continue
            try:
                y_value = extract_y_value(run_result)
            except (TypeError, ValueError):
                continue
            series_name = f"{solver_name} | {folder}"
            grouped[series_name].append((filename, y_value))

    return grouped


def filter_series_by_solvers(
    series_points: dict[str, list[tuple[str, float]]],
    selected_solvers: list[str] | None,
) -> dict[str, list[tuple[str, float]]]:
    if not selected_solvers:
        return series_points

    selected = set(selected_solvers)
    filtered: dict[str, list[tuple[str, float]]] = {}
    for series_name, points in series_points.items():
        solver_name = series_name.split(" | ", maxsplit=1)[0]
        if solver_name in selected:
            filtered[series_name] = points
    return filtered


def plot_all_series(
    series_points: dict[str, list[tuple[str, float]]],
    output_path: Path,
) -> Path:
    fig, ax = plt.subplots(figsize=(16, 7))
    all_filenames = sorted(
        {filename for points in series_points.values() for filename, _ in points}
    )
    x_index = {filename: idx for idx, filename in enumerate(all_filenames)}

    for series_name in sorted(series_points):
        points = sorted(series_points[series_name], key=lambda p: p[0])
        x_values = [x_index[name] for name, _ in points]
        y_values = [value for _, value in points]
        ax.plot(x_values, y_values, marker="o", linewidth=1.2, markersize=3.5, label=series_name)

    ax.set_title("Solver benchmark: all solvers and folders")
    ax.set_xlabel("SMT file name")
    ax.set_ylabel("Timeout / runtime (sec)")
    ax.set_xticks(range(len(all_filenames)))
    ax.set_xticklabels(all_filenames)
    ax.tick_params(axis="x", rotation=75, labelsize=7)
    ax.grid(True, linestyle="--", alpha=0.3)
    ax.legend(loc="best", fontsize=8)
    fig.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=160)
    return output_path


def main() -> int:
    args = parse_args()
    results = load_results(args.input.resolve())
    series_points = collect_series(results)
    series_points = filter_series_by_solvers(series_points, args.solvers)
    if not series_points:
        raise ValueError("No plottable data found after applying solver filter.")

    output_path = plot_all_series(series_points, args.output.resolve())
    print(f"Wrote plot: {output_path}")

    if args.show:
        plt.show()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
