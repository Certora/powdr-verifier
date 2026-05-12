#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: $0 <keccak|pairing|reth>" >&2
    exit 1
fi

scenario="$1"

cd ~/

pushd verifier
git pull
popd

source .venv/bin/activate

case "$scenario" in
    keccak)
        rm -rf data/guest-keccak/ reports/guest-keccak/
        python3 verifier/orchestrate.py powdr-guest guest-keccak
        python3 verifier/orchestrate.py -j28 verify guest-keccak : :
        ;;
    pairing)
        rm -rf \
            data/guest-pairing/ \
            reports/guest-pairing/ \
            data/guest-pairing-selection/ \
            reports/guest-pairing-selection/
        python3 verifier/orchestrate.py powdr-guest guest-pairing
        python3 verifier/select_blocks.py data/guest-pairing
        python3 verifier/orchestrate.py -j28 verify guest-pairing-selection : :
        ;;
    reth)
        find data/reth-selection/ -name '*.smt2' -delete
        rm -rf reports/reth-selection/
        python3 verifier/orchestrate.py -j28 verify reth-selection : :
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
