#!/bin/bash
# Single source of truth for which Z3 this workspace uses, and the environment
# that points the Rust build at it.
#
# Layout (siblings under the workspace root, created by setup.sh):
#
#   <workspace>/z3/z3-5.1.0/   SDK: bin/z3, bin/libz3.{a,so,dylib}, include/
#   <workspace>/z3/bin/        binaries on PATH-like names, used by the Python
#                              side's generic pysmt solvers
#   <workspace>/powdr/
#   <workspace>/verifier/      this checkout
#
# Both the Rust link and the Python subprocess solvers come out of the same
# downloaded release, so they can never drift apart.
#
# Source it, don't run it:  source verifier/z3-env.sh

# Bump these two together to move the whole workspace to another release.
# Z3_VERSION is the bare dotted version (what z3-sys wants in
# Z3_SYS_Z3_VERSION); Z3_TAG is the git tag (what download_z3.py wants).
Z3_VERSION="${Z3_VERSION:-5.1.0}"
Z3_TAG="z3-$Z3_VERSION"

# Resolve the workspace root from this file's own location, so the script works
# no matter what the caller's cwd is. BASH_SOURCE is unset under zsh, which is
# the default macOS shell and so a normal thing to source this from by hand;
# the eval keeps zsh's %x prompt expansion out of bash's parser.
_z3_env_src="${BASH_SOURCE[0]:-}"
if [ -z "$_z3_env_src" ] && [ -n "${ZSH_VERSION:-}" ]; then
    _z3_env_src="$(eval 'printf %s "${(%):-%x}"')"
fi
if [ -z "$_z3_env_src" ]; then
    echo "z3-env.sh: cannot locate myself; source me from bash or zsh," >&2
    echo "or set Z3_ROOT to <workspace>/z3 explicitly." >&2
    return 1 2>/dev/null || exit 1
fi
_z3_env_dir="$(cd "$(dirname "$_z3_env_src")" && pwd)"
Z3_ROOT="${Z3_ROOT:-$(dirname "$_z3_env_dir")/z3}"
unset _z3_env_src
Z3_PREFIX="$Z3_ROOT/$Z3_TAG"
Z3_LIB_DIR="$Z3_PREFIX/bin"
Z3_BIN_DIR="$Z3_ROOT/bin"
unset _z3_env_dir

if [[ ! -f "$Z3_LIB_DIR/libz3.so" && ! -f "$Z3_LIB_DIR/libz3.dylib" && ! -f "$Z3_LIB_DIR/libz3.a" ]]; then
    echo "missing Z3 SDK at $Z3_PREFIX" >&2
    echo "run: bash ./verifier/setup.sh" >&2
    return 1 2>/dev/null || exit 1
fi

export Z3_VERSION Z3_TAG Z3_ROOT Z3_PREFIX Z3_LIB_DIR Z3_BIN_DIR

# --- what the Rust build reads (all three are upstream z3-sys interfaces) ----
#
# There is no build.rs in verifier/rust any more; z3-sys's own build script
# does the work, driven entirely by these:
#
#   Z3_LIBRARY_PATH_OVERRIDE  adds -L for our SDK, so -lz3 resolves to it
#   Z3_NO_PKG_CONFIG          stops z3-sys probing pkg-config, which would
#                             otherwise silently prefer a system/brew z3 that
#                             predates the parser-context API smt2/z3_parse.rs
#                             needs (pkg_config::Config::probe emits its own
#                             link flags as a side effect)
#   Z3_SYS_Z3_VERSION         we tell it the version rather than letting it
#                             guess; with pkg-config off it cannot detect one
export Z3_LIBRARY_PATH_OVERRIDE="$Z3_LIB_DIR"
export Z3_NO_PKG_CONFIG=1
export Z3_SYS_Z3_VERSION="$Z3_VERSION"

# Only consulted when z3-sys is built with its `bindgen` feature (we use the
# crate's pre-generated bindings), but harmless and correct to point at ours.
export Z3_SYS_Z3_HEADER="$Z3_PREFIX/include/z3.h"

# Embed the SDK in the binaries' runtime search path. This is what the old
# per-crate build.rs did with cargo:rustc-link-arg; RUSTFLAGS reaches the same
# place without a build script. Deliberately *not* LD_LIBRARY_PATH: that would
# also apply to python3 and hijack the z3-solver package's own bundled libz3.
_z3_rpath="-C link-arg=-Wl,-rpath,$Z3_LIB_DIR"
case " ${RUSTFLAGS:-} " in
    *" $_z3_rpath "*) ;;  # already applied; don't duplicate on a re-source
    *) export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }$_z3_rpath" ;;
esac
unset _z3_rpath
