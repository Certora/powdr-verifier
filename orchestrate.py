import argparse
import itertools
import logging
import subprocess
from pathlib import Path

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

if not DATA_DIR.exists():
    DATA_DIR.mkdir(parents=True)
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
        "APC_EXPORT_LEVEL=3",
        f"cargo test {test} -- --no-capture --exact",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(' '.join(cmd), shell=True, cwd=POWDR_DIR, check=True)
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
        ], check=True)

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
        ], check=True)

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
        ], check=True)

def run_verify(first, pairs):
    for a,b in pairs:
        subprocess.run([
            "python3", VERIFIER_DIR / "main.py",
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
                for file in DATA_DIR.glob(f"{args.test}_*"):
                    file.unlink()
            run_powdr(args.test)
            exit(0)

    files = sorted(DATA_DIR.glob(f"{args.test}_*.json"))
    if not files:
        logging.warning(f"no files found for {args.test}, did you run powdr?")

    match args.command:
        case 'trace-first': run_trace(files[0])
        case 'trace-last': run_trace(files[-1])
        case 'trace-all': run_trace(*files)

        case 'evaluate-first': run_evaluate(files[0])
        case 'evaluate-last': run_evaluate(files[-1])
        case 'evaluate-all': run_evaluate(*files)

        case 'eval-first': run_eval(files[0])
        case 'eval-last': run_eval(files[-1])
        case 'eval-all': run_eval(*files)

        case 'verify-end2end': run_verify(files[0], [(files[0], files[-1])])
        case 'verify-stepwise': run_verify(files[0], itertools.pairwise(files))

        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
