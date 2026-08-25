#!/bin/bash

# git clone git@github.com:Certora/powdr-verifier.git verifier/

git clone https://github.com/powdr-labs/powdr.git

sudo apt install python3-venv
python3 -m venv .venv
source .venv/bin/activate
pip install -r verifier/requirements.txt
pysmt-install --z3 --confirm-agreement

mkdir -p ~/bin/ ~/lib/
python3 verifier/download_z3.py z3-4.16.0 --sdk ~/lib/z3-4.16.0 --bindir ~/bin
python3 verifier/download_z3.py Nightly --bindir ~/bin
chmod +x ~/bin/*

sudo apt install -y build-essential m4 pkg-config clang nasm
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"

source verifier/ec2-z3-env.sh

cd verifier/rust
cargo build --release -p simplifier
cargo build --release -p checker
cd ../..

python3 verifier/orchestrate.py powdr-guest guest-keccak
