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
    parser.add_argument('tests', type=str, nargs='+', default=['single_add_1'])

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
            logging.info(f"running tracer on {args.input}")
            input = load_json(args.input, 'input')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            trace(smt)

        case 'eval':
            logging.info(f"evaluating trace from {args.model} on {args.input}")
            input = load_json(args.input, 'input')
            model = load_json(args.model, 'model')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            evaluate(input["machine"], smt, model)

        case 'verify':
            logging.info(f"verify equivalence of {args.input_before} and {args.input_after}")
            before = load_json(args.input_before, 'Before')
            after = load_json(args.input_after, 'After')

            before_block = BasicBlock(before["block"])
            assert before_block == BasicBlock(after["block"]), "The basic block has changed"

            verify(before, after, before_block)
        case _:
            logging.error(f"unknown command: {args.command}")
            exit(1)
