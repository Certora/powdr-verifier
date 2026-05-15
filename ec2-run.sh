#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: $0 <keccak|pairing|reth>" >&2
    exit 1
fi

scenario="$1"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

cd ~/

pushd verifier
git pull
popd

source .venv/bin/activate

case "$scenario" in
    keccak)
        rm -rf "$script_dir/powdr-dumps/guest-keccak/" "$script_dir/reports/guest-keccak/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-keccak
        python3 "$script_dir/orchestrate.py" -j28 verify guest-keccak : :
        ;;
    pairing)
        rm -rf \
            "$script_dir/powdr-dumps/guest-pairing/" \
            "$script_dir/reports/guest-pairing/" \
            "$script_dir/powdr-dumps/guest-pairing-selection/" \
            "$script_dir/reports/guest-pairing-selection/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-pairing
        python3 "$script_dir/select_blocks.py" "$script_dir/powdr-dumps/guest-pairing"
        python3 "$script_dir/orchestrate.py" -j28 verify guest-pairing-selection : :
        ;;
    reth)
        find "$script_dir/data/reth-selection/" -name '*.smt2' -delete
        rm -rf "$script_dir/reports/reth-selection/"
        python3 "$script_dir/orchestrate.py" -j28 verify reth-selection : :
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
