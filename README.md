# powdr-verifier

Formal equivalence checking for [powdr](https://github.com/powdr-labs/powdr)'s
automatic precompile (APC) optimizer, via SMT.

powdr compiles RISC-V programs into OpenVM circuits and then optimizes them
through a sequence of named passes (`remove_free`, `inlining`, `memory`,
`loop_iteration`, ...). Each pass is a rewrite that's supposed to preserve
program semantics — but "supposed to" isn't a proof. This repo takes the
circuit dump from before and after any one pass, encodes both into SMT, and
asks a solver to either confirm they're behaviorally equivalent or produce a
concrete counterexample showing they aren't.

Two independent properties are checked for every pass:

- **Soundness** — the optimized circuit doesn't accept anything the original
  circuit would have rejected.
- **Completeness** — the optimized circuit doesn't reject anything the
  original circuit would have accepted.

Both come back `unsat` (no counterexample exists) when a pass is genuinely
sound; `sat` means the solver found a model exhibiting a real behavioral
difference.

## Quickstart

This repo needs a sibling checkout of
[`powdr-labs/powdr`](https://github.com/powdr-labs/powdr) itself — that's
where the circuits actually get built. `setup.sh` clones it for you; run it
from the workspace directory that holds this checkout, not from inside it:

```sh
mkdir verifier-root && cd verifier-root
git clone https://github.com/Certora/powdr-verifier.git verifier
bash ./verifier/setup.sh
```

`setup.sh` checks for the tools you need (a C toolchain, `m4`,
`autoconf`/`automake` — FLINT builds from source —
[`uv`](https://docs.astral.sh/uv/), Rust) and tells you what to install if
anything's missing; it never runs `sudo` on your behalf. Once everything's
present it clones `powdr`, runs `uv sync` (which provisions its own Python if
needed — no system Python required), downloads the pinned z3 SDK, builds the
Rust helper binaries, and runs a smoke test. (On a disposable box you control
fully, `ec2-setup.sh` does the same thing but installs missing packages for
you automatically.)

Everything lands inside the workspace directory — nothing is written to
`~/bin` or `~/lib`:

```
verifier-root/
  powdr/            cloned by setup.sh
  verifier/         this repo
  z3/               the pinned z3: SDK the Rust side links, binary the solvers run
```

To rebuild the Rust workspace later, `cd verifier/rust && just build`. It
needs the environment `verifier/z3-env.sh` exports, which the recipe sources
for you; a bare `cargo build` without it fails at link time with
`ld: library 'z3' not found`.

## Basic usage

Build a benchmark and verify one pass of it (from inside `verifier/`):

```sh
uv run python3 orchestrate.py powdr-guest guest-keccak  # build the circuit, export APC dumps
uv run python3 orchestrate.py verify guest-keccak 0     # verify the first optimizer pass
```

The trailing arguments select what to verify. One argument is a *step* (which
optimizer pass); two are *block* then *step*; each accepts a single index or
an `a:b` range, and omitting them verifies everything:

```sh
uv run python3 orchestrate.py verify guest-keccak            # every pass of every block
uv run python3 orchestrate.py verify guest-keccak 0:3        # first three passes, every block
uv run python3 orchestrate.py verify guest-keccak 2099512 0  # one block, first pass
```

Blocks are named by the ids in the dump filenames
(`apc_candidate_<block>_<step>_<pass>.json`) — program addresses like
`2099512`, **not** 0-based indices. `verify guest-keccak 0 0` therefore selects
block 0, which does not exist, and reports `no files found ... did you run
powdr?` even when the dumps are fine. Use `ls powdr-dumps/<test>/` to see the
block ids you have.

Or drive a single equivalence check by hand. `--base-dump` is required and
must come *before* the subcommand: only the step-0 dump carries the block
definition that later dumps are diffed against.

```sh
uv run python3 main.py --base-dump dumps/apc_candidate_2099512_000_unopt.json \
    verify before.json after.json out.smt2   # writes out.{soundness,completeness}.smt2
uv run python3 main.py check out.soundness.smt2
```

Note that `orchestrate.py verify` also runs the simplifier between those two
steps; checking the raw encoding by hand is much more likely to come back
`unknown-timeout`.

## How it fits together

```
powdr build  →  apc_candidate_*.json dumps (one per optimizer pass)
             →  SMT encoding (constraints / consequences / axioms)
             →  soundness + completeness checks, run through z3
             →  HTML report
```

The Python side (`src/`) owns the SMT encoding and orchestration; a small
Rust workspace (`rust/`) reimplements the hottest simplification and
checking steps for speed.

## Documentation

**[DEVELOPER.md](DEVELOPER.md)** has the full picture: the core SMT
data model and why it's structured the way it is, every CLI entry point,
the bus-interaction encoders and the soundness pitfalls they're built to
avoid, the simplifier/checker pipelines, the `lens`/`membus` inspection
tools, testing, and CI. Start there for anything beyond a quick look.

## Testing

```sh
uv run pytest                                     # unit tests + declarative regression cases
uv run ruff format --diff . && uv run ruff check .
```

## License

MIT — see [LICENSE](LICENSE).
