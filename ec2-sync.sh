#!/bin/bash

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "usage: $0 <upload-reth|keccak|keccak-selection|pairing|reth|reports>" >&2
    exit 1
fi

scenario="$1"

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
benchmarks_dir="$(cd -- "$script_dir/../powdr-verifier-benchmarks" && pwd)"

archive_report() {
    local src="$1"
    local report_dir="$2"
    local stem name report_ts
    stem="$(basename "${src%.html}")"
    if [ -f "$report_dir/job.json" ]; then
        report_ts="$(python3 -c "
import json, sys
from datetime import datetime, timezone
from pathlib import Path
job = json.loads(Path(sys.argv[1]).read_text())
dt = datetime.fromisoformat(job['started_at'])
if dt.tzinfo is not None:
    dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
print(dt.strftime('%Y%m%d-%H%M%S'))
" "$report_dir/job.json")"
    else
        report_ts="$(date -u +%Y%m%d-%H%M%S)"
    fi
    name="${stem}-${report_ts}"
    mkdir -p "$benchmarks_dir"
    cp -- "$src" "$benchmarks_dir/${name}.html"
    cp -- "${src%.html}.db" "$benchmarks_dir/${name}.db"
    echo "archived ${name}.html and ${name}.db -> powdr-verifier-benchmarks/"
}

download() {
    local remote_powdr_dumps="$1"
    local remote_reports="$2"
    local local_powdr_dumps_dir="$3"
    local local_reports_dir="$4"

    mkdir -p "$local_powdr_dumps_dir" "$local_reports_dir"
    rsync -avP --delete "ec2-powdr-rsync:$remote_powdr_dumps" "$local_powdr_dumps_dir/"
    rsync -avP --delete "ec2-powdr-rsync:$remote_reports" "$local_reports_dir/"
}

case "$scenario" in
    upload-reth)
        rsync -avP --delete "$script_dir/data/reth-selection/" "ec2-powdr-rsync:verifier/data/reth-selection/"
        ;;
    keccak)
        download \
            "verifier/powdr-dumps/guest-keccak/" \
            "verifier/reports/guest-keccak/" \
            "$script_dir/powdr-dumps/guest-keccak" \
            "$script_dir/reports/guest-keccak"
        ;;
    keccak-selection)
        download \
            "verifier/powdr-dumps/guest-keccak-selection/" \
            "verifier/reports/guest-keccak-selection/" \
            "$script_dir/powdr-dumps/guest-keccak-selection" \
            "$script_dir/reports/guest-keccak-selection"
        ;;
    pairing)
        download \
            "verifier/powdr-dumps/guest-pairing-selection/" \
            "verifier/reports/guest-pairing-selection/" \
            "$script_dir/powdr-dumps/guest-pairing-selection" \
            "$script_dir/reports/guest-pairing-selection"
        ;;
    reth)
        download \
            "verifier/powdr-dumps/reth-selection/" \
            "verifier/reports/reth-selection/" \
            "$script_dir/powdr-dumps/reth-selection" \
            "$script_dir/reports/reth-selection"
        ;;
    reports)
        echo "report guest-keccak"
        #python3 "$script_dir/main.py" report "$script_dir/reports/guest-keccak" "$script_dir/report-keccak.html"
        #archive_report "$script_dir/report-keccak.html" "$script_dir/reports/guest-keccak"
        echo "report guest-keccak-selection"
        python3 "$script_dir/main.py" report "$script_dir/reports/guest-keccak-selection" "$script_dir/report-keccak-selection.html"
        archive_report "$script_dir/report-keccak-selection.html" "$script_dir/reports/guest-keccak-selection"
        echo "report guest-pairing-selection"
        #python3 "$script_dir/main.py" report "$script_dir/reports/guest-pairing-selection" "$script_dir/report-pairing.html"
        #archive_report "$script_dir/report-pairing.html" "$script_dir/reports/guest-pairing-selection"
        echo "report reth-selection"
        #python3 "$script_dir/main.py" report "$script_dir/reports/reth-selection" "$script_dir/report-reth.html"
        #archive_report "$script_dir/report-reth.html" "$script_dir/reports/reth-selection"
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
