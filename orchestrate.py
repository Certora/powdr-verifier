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

    sub = parser.add_subparsers(dest="command")
    
    sub_trace = sub.add_parser('trace')
    sub_trace.add_argument('test', type=str, default='single_add_1')

    sub_traceall = sub.add_parser('trace-all')
    sub_traceall.add_argument('test', type=str, default='single_add_1')

    sub_eval = sub.add_parser('eval')
    sub_eval.add_argument('test', type=str, default='single_add_1')

    sub_verify = sub.add_parser('verify-end2end')
    sub_verify.add_argument('test', type=str, default='single_add_1')

    sub_verifyall = sub.add_parser('verify-stepwise')
    sub_verifyall.add_argument('test', type=str, default='single_add_1')

    sub_ppsmt = sub.add_parser('preprocess')
    sub_ppsmt.add_argument('file', type=Path)

    return parser.parse_args()


def run_powdr(test):
    cmd = [
        f"APC_EXPORT_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True)} APC_EXPORT_LEVEL=2 cargo test {test} -- --no-capture --exact"
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(cmd, shell=True, cwd=POWDR_DIR)

def run_verifier():
    subprocess.run([
        "python3", VERIFIER_DIR / "main.py", "--dump-smt", "verify", DATA_DIR / "apc_candidate_unopt_0.json", DATA_DIR / "apc_candidate_0.json"
    ])


if __name__ == '__main__':
    args = parse_args()

    files = sorted(list(DATA_DIR.glob("apc_candidate_0_*.json")))
    first = files[0]
    last = files[-1]

    match args.command:
        case 'trace':
            run_powdr(args.test)
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", first,
                "trace",
                last,
                "--dump-model", last.with_suffix(".model"),
            ])

        case 'trace-all':
            run_powdr(args.test)
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
            run_powdr(args.test)
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
            run_powdr(args.test)
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", first,
                "verify",
                first,
                last,
            ])

        case 'verify-stepwise':
            run_powdr(args.test)
            for a,b in itertools.pairwise(files):
                subprocess.run([
                    "python3", VERIFIER_DIR / "main.py",
                    "--dump-smt",
                    "--base-dump", first,
                    "verify",
                    a,
                    b,
                ])
        
        case 'preprocess':
            subprocess.run([
                "cvc5/build/bin/cvc5",
                "--preprocess-only",
                "-o", "post-asserts",
                args.file,
            ])

        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
