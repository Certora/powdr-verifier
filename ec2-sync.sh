#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: $0 <upload-reth|keccak|pairing|reth|reports>" >&2
    exit 1
fi

scenario="$1"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$script_dir/.." && pwd)"

download() {
    local remote_glob="$1"
    local remote_reports="$2"
    local local_data_dir="$3"
    local local_reports_dir="$4"

    mkdir -p "$local_data_dir" "$local_reports_dir"
    rsync -avP --delete "ec2-powdr-rsync:$remote_glob" "$local_data_dir/"
    rsync -avP --delete "ec2-powdr-rsync:$remote_reports" "$local_reports_dir/"
}

case "$scenario" in
    upload-reth)
        rsync -avP --delete "$root_dir/data/reth-selection/" "ec2-powdr-rsync:data/reth-selection/"
        ;;
    keccak)
        download \
            "data/guest-keccak/*.json" \
            "reports/guest-keccak/" \
            "$root_dir/data/guest-keccak" \
            "$root_dir/reports/guest-keccak"
        ;;
    pairing)
        download \
            "data/guest-pairing-selection/*.json" \
            "reports/guest-pairing-selection/" \
            "$root_dir/data/guest-pairing-selection" \
            "$root_dir/reports/guest-pairing-selection"
        ;;
    reth)
        download \
            "data/reth-selection/*.json" \
            "reports/reth-selection/" \
            "$root_dir/data/reth-selection" \
            "$root_dir/reports/reth-selection"
        ;;
    reports)
        echo "report guest-keccak"
        python3 "$script_dir/main.py" report "$root_dir/reports/guest-keccak" "$root_dir/report-keccak.html"
        echo "report guest-pairing-selection"
        python3 "$script_dir/main.py" report "$root_dir/reports/guest-pairing-selection" "$root_dir/report-pairing.html"
        echo "report reth-selection"
        python3 "$script_dir/main.py" report "$root_dir/reports/reth-selection" "$root_dir/report-reth.html"
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
