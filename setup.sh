#!/bin/bash
set -euo pipefail

# Like ec2-setup.sh, but for a workstation you don't want a script silently
# installing system packages onto: this only checks for what's needed and
# tells you what to run yourself, then does everything else automatically.
#
# Run from the workspace root, with this repo already checked out into
# verifier/ -- i.e.
#
#   mkdir verifier-root && cd verifier-root
#   git clone git@github.com:Certora/powdr-verifier.git verifier/
#   bash ./verifier/setup.sh
#
# and you end up with powdr/, z3/ and verifier/ as siblings. Nothing is written
# outside the workspace root.

os="$(uname -s)"
need() { command -v "$1" >/dev/null 2>&1; }

# clang/make come from Xcode Command Line Tools on macOS, not brew, so they're
# tracked separately from the packages a package manager can actually install.
missing_pkgs=()
missing_notes=()

need git        || missing_pkgs+=(git)
need m4         || missing_pkgs+=(m4)
#need libtool    || missing_pkgs+=(libtool)
need autoconf   || missing_pkgs+=(autoconf)
need automake   || missing_pkgs+=(automake)

if [ "$os" = "Darwin" ]; then
    { need clang && need make; } || missing_notes+=("Xcode Command Line Tools (clang, make): xcode-select --install")
else
    need clang || missing_pkgs+=(clang)
    need make || missing_pkgs+=(make)
fi

if [ "${#missing_pkgs[@]}" -gt 0 ] || [ "${#missing_notes[@]}" -gt 0 ]; then
    echo "Missing required tools:" >&2
    for note in "${missing_notes[@]}"; do
        echo "  $note" >&2
    done
    if [ "${#missing_pkgs[@]}" -gt 0 ]; then
        if [ "$os" = "Darwin" ]; then
            echo "  brew install ${missing_pkgs[*]}" >&2
        else
            echo "  sudo apt install ${missing_pkgs[*]}" >&2
        fi
    fi
    echo >&2
    echo "Then re-run this script." >&2
    exit 1
fi

if ! need cargo; then
    echo "Rust not found. Install it yourself, e.g.:" >&2
    echo "  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh" >&2
    echo "Then re-run this script." >&2
    exit 1
fi

if ! need uv; then
    echo "uv not found. Install it yourself, e.g.:" >&2
    echo "  curl -LsSf https://astral.sh/uv/install.sh | sh" >&2
    echo "Then re-run this script." >&2
    exit 1
fi

if [ ! -d powdr ]; then
    git clone https://github.com/powdr-labs/powdr.git
fi

# manages its own venv (verifier/.venv) and, if needed, its own Python
# interpreter — no system python3/pip required
(cd verifier && uv sync)

# z3-env.sh owns the version; asking it first keeps the pinned release named
# in exactly one place. It exits non-zero until the SDK exists, so read the
# variables out of it rather than sourcing it here.
z3_version="$(sed -n 's/^Z3_VERSION="\${Z3_VERSION:-\(.*\)}"$/\1/p' verifier/z3-env.sh)"
[ -n "$z3_version" ] || { echo "could not read Z3_VERSION from verifier/z3-env.sh" >&2; exit 1; }

# One download serves both consumers: bin/libz3.* is what the Rust workspace
# links against, and bin/z3 is the binary the Python side shells out to. They
# come out of the same archive, so they cannot drift apart.
uv run --project verifier python3 verifier/download_z3.py \
    "z3-$z3_version" --sdk "z3/z3-$z3_version" --bindir z3/bin
# the default --solver is z3-nightly; it is a separate, deliberately-newer build
uv run --project verifier python3 verifier/download_z3.py Nightly --bindir z3/bin

source verifier/z3-env.sh

cd verifier/rust
cargo build --release -p simplifier
cargo build --release -p checker
cd ../..

uv run --project verifier python3 verifier/orchestrate.py powdr-guest guest-keccak
