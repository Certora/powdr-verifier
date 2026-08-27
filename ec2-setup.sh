#!/bin/bash

# git clone git@github.com:Certora/powdr-verifier.git verifier/

git clone https://github.com/powdr-labs/powdr.git

curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.local/bin:$PATH"

# manages its own venv (verifier/.venv) and, if needed, its own Python
# interpreter — no system python3/pip required
(cd verifier && uv sync)

mkdir -p ~/bin/ ~/lib/
uv run --project verifier python3 verifier/download_z3.py z3-4.16.0 --sdk ~/lib/z3-4.16.0 --bindir ~/bin
uv run --project verifier python3 verifier/download_z3.py Nightly --bindir ~/bin
chmod +x ~/bin/*

sudo apt install -y build-essential m4 pkg-config clang nasm libtool
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"

source verifier/ec2-z3-env.sh

cd verifier/rust
cargo build --release -p simplifier
cargo build --release -p checker
cd ../..

uv run --project verifier python3 verifier/orchestrate.py powdr-guest guest-keccak
