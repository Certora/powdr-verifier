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
    parser.add_argument('--clean', action='store_true')

    sub = parser.add_subparsers(dest="command")
    
    sub_trace = sub.add_parser('trace')
    sub_trace.add_argument('test', type=str)

    sub_traceall = sub.add_parser('trace-all')
    sub_traceall.add_argument('test', type=str)

    sub_eval = sub.add_parser('eval')
    sub_eval.add_argument('test', type=str)

    sub_verify = sub.add_parser('verify-end2end')
    sub_verify.add_argument('test', type=str)

    sub_verifyall = sub.add_parser('verify-stepwise')
    sub_verifyall.add_argument('test', type=str)

    sub_ppsmt = sub.add_parser('preprocess')
    sub_ppsmt.add_argument('file', type=Path)

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
        new = file.with_name(file.name.replace("apc_candidate", test))
        file.rename(new)
        if new.suffix == ".json":
            yield new

if __name__ == '__main__':
    args = parse_args()

    if args.clean:
        for file in DATA_DIR.glob(f"{args.test}_*"):
            file.unlink()

    files = sorted(run_powdr(args.test))
    first = files[0]
    last = files[-1]

    match args.command:
        case 'trace':
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "-v",
                "--skip-memory-analysis",
                "--dump-smt",
                "--base-dump", first,
                "trace",
                first,
                "--dump-model", last.with_suffix(".model"),
            ])

        case 'trace-all':
            for f in files:
                subprocess.run([
                    "python3", VERIFIER_DIR / "main.py",
                    "--dump-smt",
                    "--base-dump", first,
                    "trace",
                    f,
                    "--dump-model", f.with_suffix(".model"),
                ])

        case 'eval':
            model = last.with_suffix(".model")
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", first,
                "trace",
                last,
                "--dump-model", model,
            ])
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "eval",
                last,
                model,
            ])

        case 'verify-end2end':
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", first,
                "verify",
                first,
                last,
            ])

        case 'verify-stepwise':
            for a,b in itertools.pairwise(files):
                subprocess.run([
                    "python3", VERIFIER_DIR / "main.py",
                    "--dump-smt",
                    "--base-dump", first,
                    "verify",
                    a,
                    b,
                ])

        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
