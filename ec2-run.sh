#!/bin/bash

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "usage: $0 <keccak|keccak-selection|pairing|reth> [verify-args...]" >&2
    exit 1
fi

scenario="$1"
shift 1

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

list_trace_block_ids_every_fifth() {
    ls $script_dir/powdr-dumps/$1/apc_candidate_*.json \
    | sed -n 's/.*apc_candidate_\([0-9]*\)_.*/\1/p' \
    | sort -nu \
    | awk 'NR % 5 == 1'
}

cd ~/

pushd verifier
git pull
popd

source .venv/bin/activate

case "$scenario" in
    keccak)
        rm -rf "$script_dir/powdr-dumps/guest-keccak/"
        rm -rf "$script_dir/data/guest-keccak/"
        rm -rf "$script_dir/reports/guest-keccak/"
        python3 "$script_dir/orchestrate.py" powdr-guest guest-keccak
        python3 "$script_dir/orchestrate.py" -j28 verify guest-keccak : : "$@"
        for bid in $(list_trace_block_ids_every_fifth guest-keccak); do
            python3 "$script_dir/orchestrate.py" -j28 trace guest-keccak ${bid} : "$@"
        done
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
        for bid in $(list_trace_block_ids_every_fifth guest-keccak-selection); do
            python3 "$script_dir/orchestrate.py" -j28 trace guest-keccak-selection ${bid} : "$@"
        done
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
        for bid in $(list_trace_block_ids_every_fifth guest-pairing); do
            python3 "$script_dir/orchestrate.py" -j28 trace guest-pairing ${bid} : "$@"
        done
        ;;
    reth)
        rm -rf "$script_dir/data/reth-selection/"
        rm -rf "$script_dir/reports/reth-selection/"
        python3 "$script_dir/orchestrate.py" -j28 verify reth-selection : : "$@"
        for bid in $(list_trace_block_ids_every_fifth reth-selection); do
            python3 "$script_dir/orchestrate.py" -j28 trace reth-selection ${bid} : "$@"
        done
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
