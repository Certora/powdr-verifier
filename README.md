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
where the circuits actually get built. From an empty workspace directory:

```sh
git clone https://github.com/Certora/powdr-verifier.git verifier
./verifier/setup.sh
```

`setup.sh` checks for the tools you need (a C toolchain, `pkg-config`, `m4`,
`nasm`, `libtool`, `autoconf`/`automake`, Python 3 with `venv`, Rust) and
tells you what to install if anything's missing — it never runs `sudo` on
your behalf. Once everything's present, it clones `powdr` as a sibling
directory, sets up a Python venv, downloads a z3 SDK, builds the Rust
helper binaries, and runs a smoke test. (On a disposable box you control
fully, `ec2-setup.sh` does the same thing but installs missing packages for
you automatically.)

## Basic usage

Build a benchmark and verify one pass of it:

```sh
python3 orchestrate.py powdr-guest guest-keccak # build the circuit, export APC dumps
python3 orchestrate.py verify guest-keccak 0 0  # verify block 0's first optimizer pass
```

Or drive a single equivalence check by hand:

```sh
python3 main.py verify before.json after.json out.smt2
python3 main.py check out.soundness.smt2
```

## How it fits together

```
powdr build  →  apc_candidate_*.json dumps (one per optimizer pass)
             →  SMT encoding (constraints / consequences / axioms)
             →  soundness + completeness checks, run through z3
             →  HTML report
```

The Python side (`src/`) owns the SMT encoding and orchestration; a small
Rust workspace (`rust/`) reimplements the hottest simplification and
checking steps for speed. A large tree of proof obligations
(`audit/rewrite-rules/`) independently certifies that every simplification
pass is sound.

## Documentation

**[DEVELOPER.md](DEVELOPER.md)** has the full picture: the core SMT
data model and why it's structured the way it is, every CLI entry point,
the bus-interaction encoders and the soundness pitfalls they're built to
avoid, the simplifier/checker pipelines, the `lens`/`membus` inspection
tools, testing, and CI. Start there for anything beyond a quick look.

## Testing

```sh
pytest              # unit tests + declarative regression cases
ruff format --diff . && ruff check .
```

## License

MIT — see [LICENSE](LICENSE).
