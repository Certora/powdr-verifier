#!/bin/bash

# git clone git@github.com:Certora/powdr-verifier.git verifier/

git clone https://github.com/powdr-labs/powdr.git

curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.local/bin:$PATH"

# manages its own venv (verifier/.venv) and, if needed, its own Python
# interpreter — no system python3/pip required
(cd verifier && uv sync)

z3_version="$(sed -n 's/^Z3_VERSION="\${Z3_VERSION:-\(.*\)}"$/\1/p' verifier/z3-env.sh)"
uv run --project verifier python3 verifier/download_z3.py \
    "z3-$z3_version" --sdk "z3/z3-$z3_version" --bindir z3/bin
uv run --project verifier python3 verifier/download_z3.py Nightly --bindir z3/bin

sudo apt install -y build-essential m4 clang libtool
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"

source verifier/z3-env.sh

cd verifier/rust
cargo build --release -p simplifier
cargo build --release -p checker
cd ../..

uv run --project verifier python3 verifier/orchestrate.py powdr-guest guest-keccak
