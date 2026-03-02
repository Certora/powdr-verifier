import argparse
import itertools
import logging
import shutil
import subprocess
import sys
from pathlib import Path

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

if not DATA_DIR.exists():
    DATA_DIR.mkdir(parents=True)
assert POWDR_DIR.exists()
assert VERIFIER_DIR.exists()

_ARGS = None
PYTHON = sys.executable


def parse_range(ls, selectors):
    if not selectors:
        yield from ls

    def int_or_None(s):
        return None if s == "" else int(s)

    for selector in selectors:
        match selector.split(":", maxsplit=1):
            case [start, stop]:
                yield from ls[int_or_None(start):int_or_None(stop)]
            case [index]:
                yield ls[int(index)]
            case _:
                raise ValueError(f"invalid slice: {selector}")

def parse_paired_range(ls, selectors):
    if not selectors:
        yield ls[0], ls[-1]

    def start_int(s):
        return None if s == "" else int(s)
    def stop_int(s):
        return None if s == "" else int(s) + 1

    for selector in selectors:
        match selector.split(":", maxsplit=1):
            case [start, stop]:
                yield from itertools.pairwise(ls[start_int(start):stop_int(stop)])
            case [index]:
                match index.split("/", maxsplit=1):
                    case [first, second]:
                        yield (ls[int(first)], ls[int(second)])
                    case [id]:
                        yield (ls[int(id)], ls[int(id)+1])
                    case _:
                        raise ValueError(f"invalid slice: {selector}")
            case _:
                raise ValueError(f"invalid slice: {selector}")


def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('command', choices=[
        'powdr',
        'trace',
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
    _ARGS.additional_args = ["--dump-smt"] + leftover
    return _ARGS


def __run_main(command, *args):
    subprocess.run([
        PYTHON, VERIFIER_DIR / "main.py",
        *_ARGS.additional_args,
        command,
        *args,
    ], check=True)


def run_powdr(test):
    dir = DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True) / test
    patch = None
    if _ARGS.with_patch is not None:
        patch = _ARGS.with_patch.resolve()
    try:
        if patch is not None:
            logging.info(f"applying {patch}")
            subprocess.run(["git", "apply", patch], cwd=POWDR_DIR, check=True)
            dir = dir.with_name(f"{dir.name}-{patch.stem}")
        cmd = [
            f"APC_EXPORT_PATH={dir}",
            "APC_EXPORT_LEVEL=3",
            f"cargo test {test} -- --no-capture --exact",
        ]
        logging.warning(f"running {' '.join(cmd)}")
        subprocess.run(" ".join(cmd), shell=True, cwd=POWDR_DIR, check=True)
    finally:
        if patch is not None:
            logging.info(f"undoing {patch}")
            subprocess.run(["git", "apply", "-R", patch], cwd=POWDR_DIR, check=True)

def run_trace(*files):
    for f in files:
        __run_main("trace", f, f.parent / f"trace-{f.stem}.smt2")

def run_evaluate(first, *files):
    for f in files:
        model = f.with_suffix(".model")
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
        model = f.with_suffix(".model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        __run_main("eval", f, model)

def run_verify(*pairs):
    for a,b in pairs:
        __run_main("verify", a, b)


if __name__ == '__main__':
    args = parse_args()

    match args.command:
        case 'powdr':
            if args.clean:
                shutil.rmtree(DATA_DIR / args.test)
            run_powdr(args.test)
            exit(0)

    files = sorted((DATA_DIR / args.test).glob("apc_candidate_0_[0-9]*.json"))
    eliminations = DATA_DIR / args.test / "apc_candidate_0_substitutions.json"

    if files:
        args.additional_args += ["--base-dump", files[0]]
    if eliminations.exists():
        args.additional_args += ["--eliminations", eliminations]

    if not files:
        logging.warning(f"no files found for {args.test}, did you run powdr?")

    try:
        match args.command:
            case 'trace':
                run_trace(*parse_range(files, args.k))
            case 'evaluate':
                run_evaluate(files[0], *parse_range(files, args.k))
            case 'eval':
                run_eval(*parse_range(files, args.k))
            case 'verify':
                run_verify(*parse_paired_range(files, args.k))

            case _:
                logging.error(f"unknown command: {args.command}")
                exit(1)
    
    except subprocess.CalledProcessError:
        pass
    except KeyboardInterrupt:
        pass
