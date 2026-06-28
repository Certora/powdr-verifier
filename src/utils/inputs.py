"""Filename parsing and grouping for batched ``apc_candidate_*`` JSON inputs."""
from collections import defaultdict
import re
import pathlib

from ..paths import dump_input_relpath

__FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")

def parse_filename(file: pathlib.Path) -> tuple[int, int, str]:
    """Parse ``apc_candidate_<block>_<idx>[<suffix>].json`` names; return ``None`` if no match."""
    if m := __FILENAMERE.match(file.name):
        return int(m.group(1)), int(m.group(2)), m.group(3) or ""
    return None


def format_passname(step: int, suffix: str) -> str:
    """Build a pass label like ``003_solver`` from step index and filename suffix."""
    name = suffix.lstrip("_")
    if name:
        return f"{step:03d}_{name}"
    return f"{step:03d}"

def load_files_by_block(basedir: pathlib.Path):
    """Index all ``apc_candidate_*.json`` under ``basedir`` by block id then candidate index."""
    files = defaultdict(dict)
    __FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
    for file in basedir.glob("apc_candidate_*.json"):
        if m := parse_filename(file):
            block,step,passname = m
            assert step not in files[block], f"{step} is already there for block {block}"
            files[block][step] = (file, passname)
            if "substitutions" not in files[block]:
                tmp = basedir / f"apc_candidate_{block}_substitutions.json"
                if tmp.exists():
                    files[block]["substitutions"] = tmp
    #for blk in files:
    #    print(blk)
    #    for i in sorted(set(files[blk].keys()) - {"substitutions"}):
    #        print(i, files[blk][i])

    return files

def load_verification_steps(basedir: pathlib.Path):
    """Pair consecutive candidate dumps per block as (before_path, after_path) verification steps."""
    blocks = load_files_by_block(basedir)
    res = {}
    for block in blocks:
        assert 0 in blocks[block]
        i = 1
        while i in blocks[block]:
            _, suffix = blocks[block][i]
            res[
                (
                    dump_input_relpath(blocks[block][i - 1][0]),
                    dump_input_relpath(blocks[block][i][0]),
                )
            ] = (
                block,
                format_passname(i, suffix),
            )
            i += 1
    return res
