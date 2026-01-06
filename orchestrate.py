import subprocess
from pathlib import Path

DATA_DIR = Path.cwd() / "data"
POWDR_DIR = Path.cwd() / "powdr"
VERIFIER_DIR = Path.cwd() / "verifier"

assert DATA_DIR.exists()
assert POWDR_DIR.exists()
assert VERIFIER_DIR.exists()

def run_powdr():
    POWDR_CONFIGS = [
        f"APC_CBOR_PATH={DATA_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True)} cargo test single_add_1"
    ]
    for config in POWDR_CONFIGS:
        print(f"Running {config}")
        subprocess.run(config, shell=True, cwd=POWDR_DIR)

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
    for cbor_file in DATA_DIR.glob("apc_candidate_0.cbor"):
        print(f"Deserializing {cbor_file}")
        deserialize(cbor_file)

run_powdr()
deserialize_all()
