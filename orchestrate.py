import argparse
import itertools
import logging
import subprocess
from pathlib import Path

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

assert DATA_DIR.exists()
assert POWDR_DIR.exists()
assert VERIFIER_DIR.exists()

def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('command', choices=[
        'powdr',
        'trace-first', 'trace-last','trace-all',
        'evaluate-first', 'evaluate-last', 'evaluate-all',
        'eval-first', 'eval-last', 'eval-all',
        'verify-end2end', 'verify-stepwise',
    ])
    parser.add_argument('test', type=str)
    parser.add_argument('--clean', action='store_true')

    return parser.parse_args()


def run_powdr(test):
    cmd = [
        f"APC_EXPORT_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True)}",
        "APC_EXPORT_LEVEL=2",
        f"cargo test {test} -- --no-capture --exact",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(' '.join(cmd), shell=True, cwd=POWDR_DIR)
    for file in DATA_DIR.glob("apc_candidate_*.*"):
        file.rename(file.with_name(file.name.replace("apc_candidate", test)))

def run_trace(*files):
    first = files[0]
    for f in files:
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            "--dump-smt",
            "--base-dump", first,
            "trace",
            f,
            "--dump-model", f.with_suffix(".model"),
        ])

def run_evaluate(*files):
    first = files[0]
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
        ])

def run_eval(*files):
    first = files[0]
    for f in files:
        model = f.with_suffix(".model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            "--base-dump", first,
            "eval",
            f,
            model,
        ])

def run_verify(first, *pairs):
    for a,b in pairs:
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
            "--dump-smt",
            "--base-dump", first,
            "verify",
            a,
            b,
        ])


if __name__ == '__main__':
    args = parse_args()

    files = sorted(DATA_DIR.glob(f"{args.test}_*.json"))
    first = files[0]
    last = files[-1]

    match args.command:
        case 'powdr':
            if args.clean:
                for file in DATA_DIR.glob(f"{args.test}_*"):
                    file.unlink()
            run_powdr(args.test)

        case 'trace-first': run_trace(first)
        case 'trace-last': run_trace(last)
        case 'trace-all': run_trace(*files)

        case 'evaluate-first': run_evaluate(first)
        case 'evaluate-last': run_evaluate(last)
        case 'evaluate-all': run_evaluate(*files)

        case 'eval-first': run_eval(first)
        case 'eval-last': run_eval(last)
        case 'eval-all': run_eval(*files)

        case 'verify-end2end': run_eval(first, (first, last))
        case 'verify-stepwise': run_eval(first, itertools.pairwise(files))

        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
