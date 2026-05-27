#!/bin/sh

# git clone git@github.com:Certora/powdr-verifier.git verifier/

git clone git@github.com:Certora/powdr.git

sudo apt install python3-venv
source .venv/bin/activate
pip install -r verifier/requirements.txt
pysmt-install --z3 --confirm-agreement

mkdir -p ~/bin/
python3 verifier/download_z3.py z3-4.16.0 ~/bin/
python3 verifier/download_z3.py Nightly ~/bin/
chmod +x ~/bin/*

sudo apt install build-essential
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
. "$HOME/.cargo/env"

python3 verifier/orchestrate.py powdr-guest guest-keccak