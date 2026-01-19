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

    sub_eval = sub.add_parser('eval')
    sub_eval.add_argument('test', type=str, default='single_add_1')

    sub_verify = sub.add_parser('verify-pair')
    sub_verify.add_argument('test', type=str, default='single_add_1')

    sub_verify = sub.add_parser('verify-full')
    sub_verify.add_argument('test', type=str, default='single_add_1')

    sub_ppsmt = sub.add_parser('preprocess')
    sub_ppsmt.add_argument('file', type=Path)

    return parser.parse_args()


def run_powdr(test):
    cmd = [
        f"APC_EXPORT_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True)} APC_EXPORT_LEVEL=2 cargo test {test} -- --no-capture"
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(cmd, shell=True, cwd=POWDR_DIR)

def deserialize(cbor_file):
    DESERIALIZE_CONFIGS = [
        ("human", ".txt"),
        ("json", ".json"),
    ]
    for (format, suffix) in DESERIALIZE_CONFIGS:
        subprocess.run([
            "cargo", "run", "--bin", "deserialize", "babybear", cbor_file.relative_to(POWDR_DIR, walk_up=True), format, DATA_DIR / (cbor_file.with_suffix(suffix).name)
        ], cwd=POWDR_DIR)

def deserialize_all():
    for cbor_file in DATA_DIR.glob("*.cbor"):
        print(f"Deserializing {cbor_file}")
        deserialize(cbor_file)

def run_verifier():
    subprocess.run([
        "python3", VERIFIER_DIR / "main.py", "--dump-smt", "verify", DATA_DIR / "apc_candidate_unopt_0.json", DATA_DIR / "apc_candidate_0.json"
    ])


if __name__ == '__main__':
    args = parse_args()

    match args.command:
        case 'trace':
            run_powdr(args.test)
            #deserialize_all()
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", DATA_DIR / "apc_candidate_0_000_unopt.json",
                "trace",
                DATA_DIR / "apc_candidate_0_000_unopt.json",
                "--dump-model", DATA_DIR / "apc_candidate_0.model",
            ])

        case 'eval':
            run_powdr(args.test)
            #deserialize_all()
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", DATA_DIR / "apc_candidate_0_000_unopt.json",
                "trace",
                DATA_DIR / "apc_candidate_0.json",
                "--dump-model", DATA_DIR / "apc_candidate_0.model",
            ])
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "eval",
                DATA_DIR / "apc_candidate_0.json",
                DATA_DIR / "apc_candidate_0.model",
            ])

        case 'verify-pair':
            run_powdr(args.test)
            #deserialize_all()
            target = sorted(list(DATA_DIR.glob("apc_candidate_0_*.json")))[-1]
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "--base-dump", DATA_DIR / "apc_candidate_0_000_unopt.json",
                "verify",
                DATA_DIR / "apc_candidate_0_000_unopt.json",
                target,
            ])

        case 'verify-full':
            run_powdr(args.test)
            files = sorted(list(DATA_DIR.glob("apc_candidate_0_*.json")))

            base = files[0]

            for a,b in itertools.pairwise(files):
                subprocess.run([
                    "python3", VERIFIER_DIR / "main.py",
                    "--dump-smt",
                    "--base-dump", base,
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
