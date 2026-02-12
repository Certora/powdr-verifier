import argparse
import itertools
import logging
import shutil
import subprocess
from pathlib import Path

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

if not DATA_DIR.exists():
    DATA_DIR.mkdir(parents=True)
assert POWDR_DIR.exists()
assert VERIFIER_DIR.exists()

_ARGS = None

def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('command', choices=[
        'powdr',
        'trace-first', 'trace-k', 'trace-last','trace-all',
        'evaluate-first', 'evaluate-k','evaluate-last', 'evaluate-all',
        'eval-first', 'eval-k', 'eval-last', 'eval-all',
        'verify-first', 'verify-k', 'verify-last',
        'verify-end2end', 'verify-stepwise',
    ])
    parser.add_argument('test', type=str)
    parser.add_argument('k', type=int, nargs='*')
    parser.add_argument('--clean', action='store_true')
    parser.add_argument("-v", "--verbose", action="count", default=0)

    global _ARGS
    _ARGS = parser.parse_args()
    _ARGS.verbose_args = ["-v"] * _ARGS.verbose
    return _ARGS


def run_powdr(test):
    cmd = [
        f"APC_EXPORT_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True) / test}",
        "APC_EXPORT_LEVEL=3",
        f"cargo test {test} -- --no-capture --exact",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(' '.join(cmd), shell=True, cwd=POWDR_DIR, check=True)

def run_trace(first, *files):
    for f in files:
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            *_ARGS.verbose_args,
            "--dump-smt",
            "--base-dump", first,
            "trace",
            f,
            "--dump-model", f.with_suffix(".model"),
        ], check=True)

def run_evaluate(first, *files):
    for f in files:
        model = f.with_suffix(".model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        subprocess.run([
            "python3", VERIFIER_DIR / "evaluate.py",
            "--base-dump", first,
            f,
            model,
        ], check=True)

def run_eval(first, *files):
    for f in files:
        model = f.with_suffix(".model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            *_ARGS.verbose_args,
            "--base-dump", first,
            "eval",
            f,
            model,
        ], check=True)

def run_verify(first, pairs):
    for a,b in pairs:
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            *_ARGS.verbose_args,
            "--dump-smt",
            "--base-dump", first,
            "verify",
            a,
            b,
        ], check=True)


if __name__ == '__main__':
    args = parse_args()

    match args.command:
        case 'powdr':
            if args.clean:
                shutil.rmtree(DATA_DIR / args.test)
            run_powdr(args.test)
            exit(0)

    files = sorted((DATA_DIR / args.test).glob("*.json"))
    if not files:
        logging.warning(f"no files found for {args.test}, did you run powdr?")

    try:
        match args.command:
            case 'trace-first': run_trace(files[0], files[0])
            case 'trace-k':
                assert all([k in range(len(files)) for k in args.k]), f"all k must be in range 0..{len(files)-1}"
                run_trace(files[0], *[files[k] for k in args.k])
            case 'trace-last': run_trace(files[0], files[-1])
            case 'trace-all': run_trace(files[0], *files)

            case 'evaluate-first': run_evaluate(files[0], files[0])
            case 'evaluate-k':
                assert all([k in range(len(files)) for k in args.k]), f"all k must be in range 0..{len(files)-1}"
                run_evaluate(files[0], *[files[k] for k in args.k])
            case 'evaluate-last': run_evaluate(files[0], files[-1])
            case 'evaluate-all': run_evaluate(files[0], *files)

            case 'eval-first': run_eval(files[0], files[0])
            case 'eval-k':
                assert all([k in range(len(files)) for k in args.k]), f"all k must be in range 0..{len(files)-1}"
                run_eval(files[0], *[files[k] for k in args.k])
            case 'eval-last': run_eval(files[0], files[-1])
            case 'eval-all': run_eval(files[0], *files)

            case 'verify-end2end': run_verify(files[0], [(files[0], files[-1])])
            case 'verify-stepwise': run_verify(files[0], itertools.pairwise(files))
            case 'verify-first': run_verify(files[0], [files[:2]])
            case 'verify-k':
                assert all([k in range(len(files)-1) for k in args.k]), f"all k must be in range 0..{len(files)-2}"
                run_verify(files[0], [(files[k], files[k+1]) for k in args.k])
            case 'verify-last': run_verify(files[0], [files[-2:]])

            case _:
                logging.error(f"unknown command: {args.command}")
                exit(1)
    
    except subprocess.CalledProcessError:
        pass
    except KeyboardInterrupt:
        pass
