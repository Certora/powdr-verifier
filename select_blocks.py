import argparse
import json
from pathlib import Path
import shutil


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("input_dir", type=Path)
    return parser.parse_args()


def reduction_ratio(apc: dict) -> float:
    cost_before = float(apc["cost_before"])
    cost_after = float(apc["cost_after"])
    if cost_before <= 0:
        return float("-inf")
    return (cost_before - cost_after) / cost_before


def block_start_pc(apc: dict) -> int:
    original_blocks = apc["original_blocks"]
    if not original_blocks:
        raise ValueError("missing original_blocks")
    block = original_blocks[0]
    if not isinstance(block, dict) or "start_pc" not in block:
        raise ValueError("missing start_pc")
    return int(block["start_pc"])


def main() -> None:
    args = parse_args()
    input_dir = args.input_dir.resolve()
    input_file = input_dir / "apc_candidates.json"

    if not input_dir.is_dir():
        raise SystemExit(f"input directory does not exist: {input_dir}")
    if not input_file.is_file():
        raise SystemExit(f"missing file: {input_file}")

    with input_file.open() as f:
        data = json.load(f)

    apcs = data["apcs"]
    selected_apcs = sorted(apcs, key=reduction_ratio, reverse=True)[:50]
    selected_ids = [block_start_pc(apc) for apc in selected_apcs]
    output_dir = input_dir.parent / f"{input_dir.name}-selection"
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    copied_files = 0
    for block_id in selected_ids:
        for path in input_dir.glob(f"apc_candidate_{block_id}_*"):
            shutil.copy2(path, output_dir / path.name)
            copied_files += 1

    print(f"selected {len(selected_apcs)} blocks")
    print(f"created {output_dir}")
    print(f"copied {copied_files} files")


if __name__ == "__main__":
    main()
