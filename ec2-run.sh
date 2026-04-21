#!/bin/bash

cd ~/

pushd verifier
git pull
popd

rm -rf data/guest-keccak/ reports/guest-keccak/

source .venv/bin/activate

python3 verifier/orchestrate.py powdr-guest guest-keccak
python3 verifier/orchestrate.py -j24 verify guest-keccak : :
