#!/bin/bash

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "usage: $0 <keccak|keccak-selection|pairing|reth> [verify-args...]" >&2
    exit 1
fi

scenario="$1"
shift 1

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

cd ~/

pushd verifier
git pull
pushd rust
cargo build --release -p simplifier
popd
popd

source .venv/bin/activate

case "$scenario" in
    keccak)
        rm -rf "$script_dir/powdr-dumps/guest-keccak/"
        rm -rf "$script_dir/data/guest-keccak/"
        rm -rf "$script_dir/reports/guest-keccak/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-keccak
        python3 "$script_dir/orchestrate.py" -j28 verify guest-keccak : : "$@"
        ;;
    keccak-selection)
        rm -rf \
            "$script_dir/powdr-dumps/guest-keccak/" \
            "$script_dir/data/guest-keccak/" \
            "$script_dir/reports/guest-keccak/" \
            "$script_dir/powdr-dumps/guest-keccak-selection/" \
            "$script_dir/data/guest-keccak-selection/" \
            "$script_dir/reports/guest-keccak-selection/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-keccak
        python3 "$script_dir/select_blocks.py" --count 10 "$script_dir/powdr-dumps/guest-keccak"
        python3 "$script_dir/orchestrate.py" -j28 verify guest-keccak-selection : : "$@"
        ;;
    pairing)
        rm -rf \
            "$script_dir/powdr-dumps/guest-pairing/" \
            "$script_dir/data/guest-pairing/" \
            "$script_dir/reports/guest-pairing/" \
            "$script_dir/powdr-dumps/guest-pairing-selection/" \
            "$script_dir/data/guest-pairing-selection/" \
            "$script_dir/reports/guest-pairing-selection/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-pairing
        python3 "$script_dir/select_blocks.py" "$script_dir/powdr-dumps/guest-pairing"
        python3 "$script_dir/orchestrate.py" -j28 verify guest-pairing-selection : : "$@"
        ;;
    reth)
        rm -rf "$script_dir/data/reth-selection/"
        rm -rf "$script_dir/reports/reth-selection/"
        python3 "$script_dir/orchestrate.py" -j28 verify reth-selection : : "$@"
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
