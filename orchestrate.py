import argparse
from collections import defaultdict
import functools
import logging
import re
import shutil
import subprocess
import sys
from pathlib import Path

from src.utils.utils import s2range

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

if not DATA_DIR.exists():
    DATA_DIR.mkdir(parents=True)
assert POWDR_DIR.exists()
assert VERIFIER_DIR.exists()

_ARGS = None
PYTHON = sys.executable

def load_files_by_block(args):
    files = defaultdict(dict)
    __FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
    for file in (DATA_DIR / args.test).glob("apc_candidate_*.json"):
        if m := __FILENAMERE.match(file.name):
            block = int(m.group(1))
            if args.blocks is None or block in args.blocks:
                step = int(m.group(2))
                assert step not in files[block]
                files[block][step] = file
                if "eliminations" not in files[block]:
                    tmp = DATA_DIR / args.test / f"apc_candidate_{block}_substitutions.json"
                    if tmp.exists():
                        files[block]["eliminations"] = tmp
    
    return files


__FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
def parse_range(files: dict, steps):
    for id in sorted([k for k in files.keys() if isinstance(k, int)]):
        if id in steps:
            yield files[id]


def parse_paired_range(files: dict, steps):
    ids = sorted([i for i in files.keys() if isinstance(i, int)])
    if steps is None:
        return (files[ids[0]], files[ids[-1]])

    for k in range(max(steps.start, min(*ids)), min(steps.stop, max(*ids))):
        if k in files and k+1 in files:
            yield (files[k], files[k+1])


def __split_args_for_main(args):
    from src.utils.args import __build_parser
    _, leftover = __build_parser(skip_subparsers=True).parse_known_args(args)
    return [a for a in args if a not in leftover], leftover


def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('command', choices=[
        'powdr',
        'powdr-guest',
        'trace',
        'diff',
        'evaluate',
        'eval',
        'verify',
    ])
    parser.add_argument('test', type=str)
    parser.add_argument('k', type=str, nargs='*')
    parser.add_argument('--clean', action='store_true')
    parser.add_argument("--with-patch", type=Path, default=None)

    global _ARGS
    _ARGS, leftover = parser.parse_known_args()
    _ARGS._main_args, _ARGS._sub_args = __split_args_for_main(leftover)
    _ARGS._additional_args = []


    _ARGS.blocks = None
    _ARGS.steps = None
    match _ARGS.k:
        case []:
            pass
        case [steps]:
            pass
            _ARGS.steps = s2range(steps)
        case [blocks, steps]:
            _ARGS.blocks = s2range(blocks)
            _ARGS.steps = s2range(steps)
        case _:
            raise ValueError(f"invalid k: {_ARGS.k}")

    return _ARGS


def __run_main(command, *args):
    cmd = [PYTHON, VERIFIER_DIR / "main.py", *_ARGS._additional_args, *_ARGS._main_args, command, *args, *_ARGS._sub_args]
    subprocess.run(cmd, check=True)

def __do_simplify(input, output, tactic="rewrite:intervals:cvc5:rewrite:intervals:rewrite"):
    logging.info(f"simplifying {input.relative_to(Path.cwd())}")
    return __run_main("simplify", input, tactic, output)

def with_patch(func):
    @functools.wraps(func)
    def wrapped(*args, **kwargs):
        patch = None
        if _ARGS.with_patch is not None:
            patch = _ARGS.with_patch.resolve()
        
        try:
            if patch is not None:
                logging.info(f"applying {patch}")
                subprocess.run(["git", "apply", patch], cwd=POWDR_DIR, check=True)
        
            return func(*args, **kwargs, dirsuffix = f"-{patch.stem}" if patch is not None else "")
        finally:
            if patch is not None:
                logging.info(f"undoing {patch}")
                subprocess.run(["git", "apply", "-R", patch], cwd=POWDR_DIR, check=True)

    return wrapped

@with_patch
def run_powdr(test, dirsuffix = ""):
    dir = DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True) / f"{test}{dirsuffix}"
    cmd = [
        f"APC_EXPORT_PATH={dir}",
        "APC_EXPORT_LEVEL=3",
        f"cargo test {test} -- --no-capture --exact",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(" ".join(cmd), shell=True, cwd=POWDR_DIR, check=True)

@with_patch
def run_powdr_guest(test, dirsuffix = ""):
    dir = DATA_DIR.relative_to(POWDR_DIR, walk_up=True) / f"{test}{dirsuffix}"
    cmd = [
        f"APC_EXPORT_PATH={dir}",
        "APC_EXPORT_LEVEL=3",
        f"cargo run --bin powdr_openvm_riscv -r compile {test} --input 1 --autoprecompiles 1",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(" ".join(cmd), shell=True, cwd=POWDR_DIR, check=True)

def run_trace(*files):
    for f in files:
        logging.warning(f"running tracer on {f.relative_to(Path.cwd())}")
        smt = f.parent / f"trace-{f.stem}.smt2"
        __run_main("trace", f, smt)
        __do_simplify(smt, smt.with_suffix(".rewrite.smt2"))
        __run_main("check", smt.with_suffix(".rewrite.smt2"), "--dump-model", smt.with_suffix(".model"))

def run_diff(*pairs):
    for a,b in pairs:
        logging.warning(f"diffing {a.relative_to(Path.cwd())} and {b.relative_to(Path.cwd())}")
        __run_main("diff", a, b)

def run_evaluate(first, *files):
    for f in files:
        model = f.parent / f"trace-{f.stem}.model"
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        subprocess.run([
            PYTHON, VERIFIER_DIR / "evaluate.py",
            "--base-dump", first,
            f,
            model,
        ], check=True)

def run_eval(*files):
    for f in files:
        model = f.parent / f"trace-{f.stem}.model"
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        logging.warning(f"evaluating trace from {model.relative_to(Path.cwd())} on {f.relative_to(Path.cwd())}")
        __run_main("eval", f, model)

def run_verify(*pairs):
    for a,b in pairs:
        logging.warning(f"verify equivalence of {a.relative_to(Path.cwd())} and {b.relative_to(Path.cwd())}")
        first = a.parent / f"verify-{a.stem}-{b.stem}.smt2"
        __run_main("verify", a, b, first)
        for file in sorted(a.parent.glob(f"{first.stem}*.smt2")):
            if file.stem.endswith(".rewrite"): continue
            logging.warning(f"solving {file.relative_to(Path.cwd())}")
            __do_simplify(file, file.with_suffix(".rewrite.smt2"), "rewrite:intervals:z3:isqf:rewrite")
            __run_main("check", file.with_suffix(".rewrite.smt2"), "--print-model")


if __name__ == '__main__':
    args = parse_args()

    match args.command:
        case 'powdr':
            if args.clean:
                shutil.rmtree(DATA_DIR / args.test)
            run_powdr(args.test)
            exit(0)
        case 'powdr-guest':
            if args.clean:
                shutil.rmtree(DATA_DIR / args.test)
            run_powdr_guest(args.test)
            exit(0)
    
    all_files = load_files_by_block(args)

    if not all_files:
        logging.warning(f"no files found for {args.test}, did you run powdr?")

    try:
        for block,files in sorted(all_files.items()):
            args._additional_args = []
            if 0 in files:
                args._additional_args += ["--base-dump", files[0]]
            if "eliminations" in files:
                args._additional_args += ["--eliminations", files["eliminations"]]

            match args.command:
                case 'trace':
                    run_trace(*parse_range(files, args.steps))
                case 'diff':
                    run_diff(*parse_paired_range(files, args.steps))
                case 'evaluate':
                    run_evaluate(files[0], *parse_range(files, args.steps))
                case 'eval':
                    run_eval(*parse_range(files, args.steps))
                case 'verify':
                    run_verify(*parse_paired_range(files, args.steps))

                case _:
                    logging.error(f"unknown command: {args.command}")
                    exit(1)
    
    except subprocess.CalledProcessError:
        pass
    except KeyboardInterrupt:
        pass
