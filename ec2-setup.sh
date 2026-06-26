#!/bin/bash

# git clone git@github.com:Certora/powdr-verifier.git verifier/

git clone git@github.com:Certora/powdr.git

sudo apt install python3-venv
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

Z3_PREFIX="$HOME/lib/z3-4.16.0"
export Z3_LIB_DIR="$Z3_PREFIX/bin"
export Z3_LIBRARY_PATH_OVERRIDE="$Z3_LIB_DIR"
export Z3_SYS_Z3_HEADER="$Z3_PREFIX/include/z3.h"
export RUSTFLAGS="-C link-arg=-Wl,-rpath,$Z3_LIB_DIR"

cd verifier/rust
cargo build --release -p simplifier
cd ../..

python3 verifier/orchestrate.py powdr-guest guest-keccak
