#!/bin/bash
# Link verifier/rust against the Z3 SDK under ~/lib/ (the Python side's
# z3-solver package only ships the bindings' shared library, not headers).
Z3_PREFIX="${Z3_PREFIX:-$HOME/lib/z3-4.16.0}"
Z3_LIB_DIR="$Z3_PREFIX/bin"
if [[ ! -f "$Z3_LIB_DIR/libz3.so" && ! -f "$Z3_LIB_DIR/libz3.a" ]]; then
    echo "missing Z3 SDK at $Z3_PREFIX" >&2
    echo "run: uv run --project verifier python3 verifier/download_z3.py z3-4.16.0 --sdk $Z3_PREFIX --bindir ~/bin" >&2
    return 1 2>/dev/null || exit 1
fi
export Z3_LIB_DIR
export Z3_LIBRARY_PATH_OVERRIDE="$Z3_LIB_DIR"
export Z3_SYS_Z3_HEADER="$Z3_PREFIX/include/z3.h"
export RUSTFLAGS="-C link-arg=-Wl,-rpath,$Z3_LIB_DIR"
