from collections import defaultdict
import re
import pathlib

__FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")

def parse_filename(file: pathlib.Path) -> tuple[int, int, str]:
    if m := __FILENAMERE.match(file.name):
        return int(m.group(1)), int(m.group(2)), m.group(3) or ""
    return None

def load_files_by_block(basedir: pathlib.Path):
    files = defaultdict(dict)
    __FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
    for file in basedir.glob("apc_candidate_*.json"):
        if m := parse_filename(file):
            block,step,passname = m
            assert step not in files[block], f"{step} is already there for block {block}"
            files[block][step] = (file, passname)
            if "eliminations" not in files[block]:
                tmp = basedir / f"apc_candidate_{block}_substitutions.json"
                if tmp.exists():
                    files[block]["eliminations"] = tmp
    #for blk in files:
    #    print(blk)
    #    for i in sorted(set(files[blk].keys()) - {"eliminations"}):
    #        print(i, files[blk][i])

    return files

def load_verification_steps(basedir: pathlib.Path):
    blocks = load_files_by_block(basedir)
    res = {}
    for block in blocks:
        assert 0 in blocks[block]
        i = 1
        while i in blocks[block]:
            res[(blocks[block][i-1][0], blocks[block][i][0])] = (block, blocks[block][i][1])
            i += 1
    return res
