#!/bin/bash
set -euo pipefail

# Like ec2-setup.sh, but for a workstation you don't want a script silently
# installing system packages onto: this only checks for what's needed and
# tells you what to run yourself, then does everything else automatically.
#
# Run from a workspace directory; clones powdr as a sibling of this checkout.
# git clone git@github.com:Certora/powdr-verifier.git verifier/

os="$(uname -s)"
need() { command -v "$1" >/dev/null 2>&1; }

# clang/make come from Xcode Command Line Tools on macOS, not brew, so they're
# tracked separately from the packages a package manager can actually install.
missing_pkgs=()
missing_notes=()

need git        || missing_pkgs+=(git)
need pkg-config || missing_pkgs+=(pkg-config)
need m4         || missing_pkgs+=(m4)
need nasm       || missing_pkgs+=(nasm)
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

mkdir -p ~/bin/ ~/lib/
uv run --project verifier python3 verifier/download_z3.py z3-4.16.0 --sdk ~/lib/z3-4.16.0 --bindir ~/bin
uv run --project verifier python3 verifier/download_z3.py Nightly --bindir ~/bin
chmod +x ~/bin/z3-*

source verifier/ec2-z3-env.sh

cd verifier/rust
cargo build --release -p simplifier
cargo build --release -p checker
cd ../..

uv run --project verifier python3 verifier/orchestrate.py powdr-guest guest-keccak
