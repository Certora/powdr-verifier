import argparse
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
    parser.add_argument('command', type=str, choices=['trace', 'eval', 'verify'])
    parser.add_argument('tests', type=str, nargs='*', default=['single_add_1'])

    return parser.parse_args()


def run_powdr(tests):
    for test in tests:
        cmd = [
            f"APC_CBOR_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True)} cargo test {test} -- --no-capture"
        ]
        logging.info(f"running {cmd}")
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

def run_tracer():
    pass

def run_evaluator():
    pass

def run_verifier():
    subprocess.run([
        "python3", VERIFIER_DIR / "main.py", "--dump-smt", "verify", DATA_DIR / "apc_candidate_unopt_0.json", DATA_DIR / "apc_candidate_0.json"
    ])


if __name__ == '__main__':
    args = parse_args()

    run_powdr(args.tests)

    match args.command:
        case 'trace':
            run_powdr(args.tests)
            deserialize_all()
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "trace",
                DATA_DIR / "apc_candidate_0.json",
                "--dump-model", DATA_DIR / "apc_candidate_0.model"
            ])

        case 'eval':
            run_powdr(args.tests)
            deserialize_all()
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "trace",
                DATA_DIR / "apc_candidate_0.json",
                "--dump-model", DATA_DIR / "apc_candidate_0.model"
            ])
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "eval",
                DATA_DIR / "apc_candidate_0.json",
                DATA_DIR / "apc_candidate_0.model",
            ])

        case 'verify':
            run_powdr(args.tests)
            deserialize_all()
            subprocess.run([
                "python3", VERIFIER_DIR / "main.py",
                "--dump-smt",
                "verify",
                DATA_DIR / "apc_candidate_unopt_0.json",
                DATA_DIR / "apc_candidate_0.json",
            ])

        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
