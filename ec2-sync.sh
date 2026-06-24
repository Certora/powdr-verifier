#!/bin/bash

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "usage: $0 <upload-reth|keccak|keccak-selection|pairing|reth|reports> [<run_id|->]" >&2
    echo "  optional run_id; '-' unsuffixed. A second word starting with '-' (except '-') is ignored as run_id." >&2
    exit 1
fi

scenario="$1"
if [ "$#" -ge 2 ] && { [ "$2" = "-" ] || [[ "$2" != -* ]]; }; then
    run_id="$2"
    if [ "$run_id" = "-" ]; then
        drsuf=""
    else
        drsuf="-${run_id}"
    fi
else
    drsuf=""
fi

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
        rsync -avP --delete "$script_dir/data/reth-selection${drsuf}/" "ec2-powdr-rsync:verifier/data/reth-selection${drsuf}/"
        ;;
    keccak)
        download \
            "verifier/powdr-dumps/guest-keccak/" \
            "verifier/reports/guest-keccak${drsuf}/" \
            "$script_dir/powdr-dumps/guest-keccak" \
            "$script_dir/reports/guest-keccak${drsuf}"
        ;;
    keccak-selection)
        download \
            "verifier/powdr-dumps/guest-keccak-selection/" \
            "verifier/reports/guest-keccak-selection${drsuf}/" \
            "$script_dir/powdr-dumps/guest-keccak-selection" \
            "$script_dir/reports/guest-keccak-selection${drsuf}"
        ;;
    pairing)
        download \
            "verifier/powdr-dumps/guest-pairing-selection/" \
            "verifier/reports/guest-pairing-selection${drsuf}/" \
            "$script_dir/powdr-dumps/guest-pairing-selection" \
            "$script_dir/reports/guest-pairing-selection${drsuf}"
        ;;
    reth)
        download \
            "verifier/powdr-dumps/reth-selection/" \
            "verifier/reports/reth-selection${drsuf}/" \
            "$script_dir/powdr-dumps/reth-selection" \
            "$script_dir/reports/reth-selection${drsuf}"
        ;;
    reports)
        main_run=()
        if [ -n "$drsuf" ]; then
            main_run=(--run-id "$run_id")
        fi
        echo "report guest-keccak"
        python3 "$script_dir/main.py" "${main_run[@]}" report "$script_dir/reports/guest-keccak${drsuf}" "$script_dir/report-keccak${drsuf}.html"
        archive_report "$script_dir/report-keccak${drsuf}.html" "$script_dir/reports/guest-keccak${drsuf}"
        echo "report guest-keccak-selection"
        python3 "$script_dir/main.py" "${main_run[@]}" report "$script_dir/reports/guest-keccak-selection${drsuf}" "$script_dir/report-keccak-selection${drsuf}.html"
        archive_report "$script_dir/report-keccak-selection${drsuf}.html" "$script_dir/reports/guest-keccak-selection${drsuf}"
        echo "report guest-pairing-selection"
        python3 "$script_dir/main.py" "${main_run[@]}" report "$script_dir/reports/guest-pairing-selection${drsuf}" "$script_dir/report-pairing${drsuf}.html"
        archive_report "$script_dir/report-pairing${drsuf}.html" "$script_dir/reports/guest-pairing-selection${drsuf}"
        echo "report reth-selection"
        python3 "$script_dir/main.py" "${main_run[@]}" report "$script_dir/reports/reth-selection${drsuf}" "$script_dir/report-reth${drsuf}.html"
        archive_report "$script_dir/report-reth${drsuf}.html" "$script_dir/reports/reth-selection${drsuf}"
        ;;
    *)
        echo "unknown scenario: $scenario" >&2
        exit 1
        ;;
esac
