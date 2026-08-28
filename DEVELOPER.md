# Developer Guide

This document is a map of the repository for engineers working on it: what the
tool does, how the pieces fit together, and where to look when you need to
change something. It intentionally favors *why* over *what* where the code's
structure encodes a soundness argument — get those wrong and the tool can
silently stop catching real bugs.

Contents:

- [What this repo does](#what-this-repo-does)
- [Repository layout](#repository-layout)
- [Getting set up](#getting-set-up)
- [Core concepts](#core-concepts)
- [The pipeline, end to end](#the-pipeline-end-to-end)
- [`main.py` subcommands](#mainpy-subcommands)
- [Bus-interaction encoders](#bus-interaction-encoders)
- [`membus` — memory-bus diagnosis, alignment, and certified extraction](#membus--memory-bus-diagnosis-alignment-and-certified-extraction)
- [The simplifier](#the-simplifier)
- [The checker](#the-checker)
- [The Rust workspace](#the-rust-workspace)
- [Reporting, inspection and debugging tools](#reporting-inspection-and-debugging-tools)
- [Testing](#testing)
- [CI](#ci)
- [Utility script reference](#utility-script-reference)
- [Known rough edges](#known-rough-edges)

## What this repo does

`powdr-verifier` checks that [powdr](https://github.com/powdr-labs/powdr)'s
optimizer — specifically its automatic precompile (APC) generation for the
OpenVM RISC-V circuit — does not change program semantics. powdr's optimizer
runs a sequence of named passes over a circuit (`remove_free`,
`substitute_bus_interactio_fields`, `inlining`, `memory`, `loop_iteration`,
...), each producing a new "APC candidate" dump. This repo takes any two
adjacent dumps (before/after one pass) and proves, via an SMT solver, that
they're behaviorally equivalent — or produces a counterexample if they
aren't.

There are two repos involved, checked out as **siblings**:

- `verifier/` (this repo) — the SMT encoding, solving, and orchestration logic.
- `powdr/` — a separate checkout of `powdr-labs/powdr` itself, whose build
  produces the APC candidate dumps this repo consumes. It's not vendored or
  submoduled in; you clone it next to `verifier/` (`setup.sh`/`ec2-setup.sh`
  do this for you, and CI checks it out under `path: powdr` alongside
  `path: verifier`).

Everything downstream — tracing, simplifying, checking, evaluating,
reporting — operates on JSON "APC dump" files produced by that separate
`powdr` build.

## Repository layout

```
verifier/
├── main.py              # single-invocation CLI: one dump (pair) in, one result out
├── orchestrate.py        # pipeline driver: runs main.py across a whole test's dumps
├── evaluate.py            # standalone model-evaluation script (used by orchestrate's `evaluate` command)
├── download_z3.py         # fetches prebuilt z3 SDKs/binaries from GitHub Releases
├── setup.sh / ec2-setup.sh # workstation / throwaway-box provisioning
├── z3-env.sh, ec2-run.sh, ec2-sync.sh  # remote-benchmark-box helpers
├── benchmark_solvers.py, plot_benchmark_results.py, select_blocks.py,
│   simplify_smt2.py, check-pp-pipeline.py, find_duplicated_ids.py  # standalone one-off tools
├── membus.py, lens.py     # thin wrappers for the src/membus, src/lens CLIs
│                          # (also installed as the `membus` / `lens` console
│                          # scripts; membus.py's path is load-bearing, see
│                          # src/verify/membus_subprocess.py)
├── src/
│   ├── smt/               # FormulaWithAxioms + SmtConverter — dump → SMT structure
│   ├── encoding/          # SMT structure → concrete SMT-LIB scripts (trace, sanity)
│   ├── bus_interactions/  # per-OpenVM-bus SMT encoders (memory, bitwise, range checks, ...)
│   ├── verifier.py         # before/after equivalence encoding (soundness + completeness)
│   ├── checker.py          # runs a script through z3, classifies the result
│   ├── simplifier.py, simplify/, rewriter/  # SMT-LIB simplification passes (Python reference impl)
│   ├── tracer.py           # single-circuit "does a valid trace exist" encoding
│   ├── evaluator.py         # evaluate a solver model against constraints
│   ├── converter.py         # dump → human-readable text
│   ├── diff.py              # before/after dump diff via `meld`
│   ├── visualizer.py         # terminal trace visualizer (bus contents over time)
│   ├── check/               # alternate checking strategies (rust.py, sliced.py, coi.py)
│   ├── verify/               # bug_injection.py (mutation testing for the verifier itself)
│   ├── report/                # SQLite-backed run telemetry → static HTML reports
│   ├── lens/, membus/           # standalone dump-inspection CLIs
│   ├── smt_backends/            # per-solver shims (pysmt is the real one; z3/cvc5 are stubs/legacy)
│   ├── utils/args.py             # shared ARGS() argparse singleton
│   └── paths.py                   # workspace layout constants (VERIFIER_DIR, POWDR_DIR, ...)
├── rust/
│   ├── smt2/         # SMT-LIB parsing/pretty-printing straight into real Z3 ASTs
│   ├── simplifier/   # fast Rust reimplementation of the hottest simplify passes
│   └── checker/      # fast Rust solver-invocation binary
├── tests/                  # pytest unit tests, mirroring src/ + tests/regression_cases/
└── .github/workflows/verify.yaml  # CI
```

## Getting set up

Run `setup.sh` (checks for required tools and tells you what to install — never
runs `sudo` itself) or `ec2-setup.sh` (assumes a throwaway box and installs
everything for you) from a workspace directory. Either way you end up with:

- this repo cloned into `verifier/`,
- `powdr-labs/powdr` cloned into a sibling `powdr/`,
- a `uv`-managed venv (`verifier/.venv`) with `pysmt`, `z3-solver`, and
  everything else declared in `verifier/pyproject.toml` installed,
- a downloaded z3 SDK in a sibling `z3/`, plus a `z3-nightly` binary,
- the Rust `simplifier`/`checker` binaries built in release mode,
- a `guest-keccak` smoke test run via `orchestrate.py` to confirm it all works.

Nothing is installed outside the workspace root: after `bash ./verifier/setup.sh`
you have `powdr/`, `z3/` and `verifier/` as siblings and nothing in `~/bin` or
`~/lib`.

```
<workspace>/
  powdr/
  verifier/                 this repo
  z3/
    z3-5.1.0/               SDK: bin/z3, bin/libz3.{a,dylib}, include/
    bin/z3-5.1.0            symlink to the SDK's binary
    bin/z3-nightly          separate, deliberately-newer build
```

The same downloaded release serves both sides: the Rust workspace links
`bin/libz3.*`, and the Python solvers shell out to `bin/z3`. They cannot drift
apart, because there is only one download.

There is a third z3 in the picture — the `z3-solver` wheel, which carries its
own bundled `libz3` for the in-process bindings (`z3_simplify`, the pysmt `z3`
solver). That one is pinned by hand in `pyproject.toml` and has to be bumped
alongside `Z3_VERSION` when the pin moves; all three are currently 5.1.0.

Before building the Rust workspace, `source verifier/z3-env.sh` — it is the
single place the pinned z3 version is named, and it exports everything the
build needs. See [The Rust workspace](#the-rust-workspace) for the underlying
linking mechanism if you're building manually.

## Core concepts

### `FormulaWithAxioms`: the five-way split

Every APC dump gets converted (`src/smt/conversion.py`'s `SmtConverter`) into
a `FormulaWithAxioms` namedtuple with five fields. Getting this split right —
and never collapsing it — is the single most important structural idea in the
codebase:

| field | meaning | asserted for both sides of an equivalence check? |
|---|---|---|
| `constraints` | things the circuit actually *commits to*: algebraic constraints and bus-interaction semantics | yes, symmetrically |
| `consequences` | facts *derived from* the constraints (e.g. "this value is a byte", inferred ranges) — true whenever constraints hold, but not themselves commitments | **no — reference side only**, as a premise |
| `axioms` | granted environment assumptions (VM-environment facts like range-table semantics) | yes, symmetrically |
| `derived` | column → list of defining equalities (a column can have more than one definition) | — |
| `globals` | symbols that must never be captured by a quantifier prefix | — |

A `consequence` is tagged with a `ConsequenceKind` (`UNTAGGED`,
`MEMORY_RECV_BYTES`, `MEMORY_TIMESTAMP_BOUNDS`, `RANGE_INFERENCE`) so
consumers can select a *class* of fact instead of guessing from a comment
string or the formula's shape — both were tried and both rot as encoders
change. **Anything that assembles a list of consequences into a formula must
go through `consequence_formulas()` / `consequences_of_kind()`
(`src/smt/utils.py`) — never splat the raw list into `And()`/`Or()` directly.**
A `Consequence` is a plain `NamedTuple`, not an `FNode`; pysmt's walker will
crash trying to treat one as a formula node. (This exact mistake — a bare
`*formula.consequences` splat in `src/encoding/trace.py` — was a real bug
fixed during this repo's open-sourcing pass; every other call site already
went through `consequence_formulas()`.)

### Why consequences are reference-side-only

`src/verifier.py`'s equivalence encoding asserts the *reference* circuit's
`consequences` as a premise but never negates the *goal* circuit's
consequences into the proof obligation (there's a deliberate dead-code
comment marking the spot: `# Not(And(*after.consequences)), # NOT HERE!`).

Why: a consequence is a fact entailed by the reference's constraints, not a
constraint itself. If it were asserted as an obligation on the *goal* side, a
value-preserving rewrite of the goal circuit (e.g. `-x → (P-1)*x`, sound
modulo the field prime `P`) could produce a formula whose raw integer value
falls outside a naively-stated range fact even though the rewrite is
semantically correct — manufacturing a spurious counterexample. Kept
reference-side-only, a consequence is always a sound premise and never
produces a false positive. The same reasoning shows up concretely in
`src/bus_interactions/openvm_memory.py`'s handling of the memory bus (see
below) — that file has the most detailed worked examples of getting this
polarity right and wrong.

### Soundness vs. completeness

For a `before`/`after` dump pair, `src/verifier.py` emits two independent SMT
queries:

- **Soundness** (`*.soundness.smt2`): every behavior of `after` is realizable
  by `before` — i.e. the optimization didn't let the circuit do something new.
- **Completeness** (`*.completeness.smt2`): every behavior of `before` is
  still realizable by `after` — i.e. the optimization didn't drop a real
  behavior.

Both go through a shared `encoding(before, after, qvars, io_relation)`
builder, with the two operands swapped between the two checks:

```
And(*before.constraints, *consequence_formulas(before.consequences),
    ForAll(qvars, Or(Not(And(*after.constraints)), Not(io_relation))),
    *before.axioms, *after.axioms)
```

Each query is expected `unsat` (no counterexample exists); a `sat` result is
a genuine soundness or completeness bug, and the model is the counterexample.

When the optimized (`after`) circuit introduces a fresh `is_valid` interface
column not present in `before` (`dump_introduces_is_valid`), two extra checks
are emitted: `is_valid=0` still admits an all-zero model
(`*.soundness.zero-is-model.smt2`), and `is_valid=0` forces every
bus-interaction multiplicity to zero
(`*.soundness.invalid-all-mult-zero.smt2`) — an inactive/gated row must touch
nothing observable.

### Bus interactions

A powdr circuit doesn't just have algebraic constraints — it also interacts
with shared "buses" (memory, bitwise-lookup tables, range checkers, the
execution bridge, program-counter lookup) that other parts of the VM read
from and write to. `src/bus_interactions/` has one encoder per bus kind; see
[Bus-interaction encoders](#bus-interaction-encoders).

## The pipeline, end to end

```
powdr build (cargo test, APC_EXPORT_LEVEL=3)
        │
        ▼
apc_candidate_<block>_<step>[_<passname>].json   (one dump per optimizer pass, per block)
apc_candidate_<block>_substitutions.json          (companion: eliminated-variable substitutions)
        │
        ├─ main.py trace          → trace-<stem>.{core,sanity}.smt2   (single-circuit sat/unsat checks)
        ├─ main.py verify a b out.smt2 --optimization-step <pass>
        │        → out.{soundness,completeness}.smt2  (before/after equivalence)
        ├─ main.py simplify <tactic> in out             (SMT-LIB rewriting, see below)
        ├─ main.py check in                             (run through z3, classify sat/unsat/timeout)
        ├─ main.py eval / evaluate.py                   (check a solver model actually satisfies things)
        └─ main.py report <dir> out.html                (render an HTML dashboard from the run telemetry)
```

`orchestrate.py` drives this whole sequence across every block/step in a
`powdr-dumps/<test>/` directory:

```sh
uv run python3 orchestrate.py [common flags] <command> <test> [block[:block] [step[:step]]] [-- main.py flags]
```

`<command>` is one of `powdr` / `powdr-guest` (run the sibling `powdr/`
checkout to produce dumps), `trace`, `diff`, `evaluate`, `eval`, or `verify`
(the main workflow: verify → simplify → check for every adjacent step pair).
`-j N` parallelizes across a shared thread pool. Many APC dump files on disk
are *partial* (only the `machine` object changed between passes) — pass
`--base-dump` (the pass-0 full dump) and `--substitutions` to reconstitute
them; `orchestrate.py` wires these automatically.

## `main.py` subcommands

`main.py` is the low-level, single-invocation entry point (`main.py <global
flags> <command> <command args>`), a thin dispatcher over one call into the
corresponding `src/` module:

| command | module | what it does |
|---|---|---|
| `trace` | `src.tracer.trace` | Encode one dump's single-circuit trace validity + sanity obligations. |
| `verify` | `src.verifier.verify` | The core soundness+completeness equivalence check between two dumps. |
| `check` | `src.checker.check` | Run an `.smt2` script through z3 (or another solver), classify the outcome. |
| `simplify` | `src.simplifier.simplify` | Run a named tactic (pipeline of rewrite passes) over an `.smt2` script. |
| `eval` | `src.evaluator.evaluate` | Evaluate a model against a dump's constraints/consequences/axioms/derived columns. |
| `diff` | `src.diff.diff` | Visual before/after dump diff via `meld`. |
| `text` | `src.converter.convert_and_print` | Render one dump as human-readable text. |
| `visualize` | `src.visualizer.visualize` | Terminal visualization of bus contents over time under a model. |
| `aliasing` | `src.encoding_analysis.analyze_aliases` | Diagnostic: enumerate consistent memory-pointer alias relations. |
| `report` | `src.report.render.report` | Render a directory of run telemetry into a static HTML report. |

Useful global flags: `--memory-encoding {array,busat,plain,interface,auto,none}`
(default `auto`, upgrades to `interface` when a plain-membus analysis
certifies perfect alignment), `--field-type` (default `babybear`),
`--solver` (default `z3-nightly`), `--default-executor {p,r}` (`r` = Rust
simplifier/checker backend by default), `--base-dump`/`--substitutions`
(reconstituting partial dumps, see above), `--inject [seed]` (mutation
testing, see [bug_injection](#bug-injection)), and a family of
`--no-memory`/`--no-bitwise`/`--no-bridge`/`--no-pclookup`/`--no-varrange`/`--no-tuprange`
toggles to disable individual bus encoders when debugging.

## Bus-interaction encoders

`src/bus_interactions/__init__.py` defines the base abstraction:
`OpenVMBusInteractionEncoder` owns one `SingleInteractionEncoder` subclass per
known OpenVM bus kind, dispatching each raw interaction record to the right
one. Every encoder contributes to two channels — **axioms** (granted
assumptions, both sides) and **consequences** (facts derived from *this
encoder's own* constraints, reference side only; see
[Core concepts](#core-concepts)).

- **`openvm_memory.py`** (the largest, most soundness-sensitive file, ~1100
  lines) — reads/writes keyed by `(address_space, pointer, timestamp)`, via
  either a permutation argument ("plain") or a busat-style interface encoding
  (`--memory-encoding`). Notable soundness history preserved in comments:
  - `MEMORY_TIMESTAMP_BOUNDS` is a **consequence**, not a constraint or axiom
    — as a constraint it dominated solve cost (hundreds of per-interaction
    obligations); as a top-level axiom it bound a *free* copy of the
    timestamp outside the `ForAll`, letting z3 pick that copy adversarially
    and manufacture a spurious soundness counterexample.
  - `MEMORY_RECV_BYTES` ("every value *read* is a byte") is granted via
    consequences, reference-side only — it's a VM-environment assumption, not
    a per-circuit commitment. The dual ("every value *written* is a byte")
    is a real **constraint** on both sides — reversing this polarity was the
    source of a real historical bug (see git history around "recv-byte
    grant").
  - Statically-certified same-block write-then-read pairs are asserted as
    circuit **constraints**, never a granted axiom — an unconditional axiom
    here previously produced a false pass (vacuous unsat) on a corrupted-dump
    test case, because it contradicted the other side's constraints.
- **`openvm_bitwise_lookup.py`** — bytes constrained via `(x, y, 0, 0)`;
  `(x, y, z, 1)` additionally asserts `z = x xor y` via an overapproximating
  uninterpreted function restricted by byte-range + a handful of algebraic
  identities, not a fully bit-level definition (a deliberate tractability
  tradeoff).
- **`openvm_variable_range_checker.py`** — bounds `x < 2^bits`. When `bits`
  is symbolic (e.g. a shift amount), it case-splits over the finite set of
  table widths rather than collapsing to the widest — over-widening
  previously threw away carry-is-zero facts and produced spurious
  completeness counterexamples on real blocks.
- **`openvm_tuple_range_checker.py`** — bounds a pair `(x, y)` against
  configured maxima.
- **`openvm_pc_lookup.py`** — a PC-keyed instruction lookup table, modeled
  via uninterpreted functions restricted to the basic block's actual
  instructions.
- **`openvm_execution_bridge.py`** / **`permutation_check.py`** — a stateful,
  timestamped permutation-check bus (shared machinery for any bus needing
  multiset-permutation + timestamp-monotonicity reasoning).
- **`memory_plain_utils.py`** — cone-of-influence and boolean-propagation
  helpers specifically for the "plain" (permutation-style) memory encoding,
  used to pre-resolve match-variable polarities before the main solve.

## `membus` — memory-bus diagnosis, alignment, and certified extraction

`membus <command> <group> <block> <step> [options]` — or equivalently
`membus.py ...` (a thin wrapper over
`src/membus/`) is a standalone CLI for investigating the memory bus (OpenVM
bus id 1) of one or two APC dumps by hand — distinct from, but designed
consistently with, the automatic memory-alignment analysis (`MemoryAnalysis`
in `src/bus_interactions/openvm_memory.py`) that runs inside `verify()`. The
two are not wired together in code — the only actual coupling is
`openvm_memory.py` importing the `TS_MAX` constant from `membus/facts.py`,
and its extensive cross-reference comments (`"[[membus/facts.py]]
Assumption.TS_BOUND"`) show the in-pipeline logic was *designed against*
membus's certified assumptions, not implemented via membus. Reach for
`membus` by hand when a `memory`-pass equivalence check fails or looks
suspicious and you need to see *why*, independently of the main pipeline.
Run `membus.py --agent` for a dense, load-bearing usage guide or
`membus.py --help` for the human version.

**The problem it solves.** A memory interaction on bus 1 is a send
(`mult=1`, a write) or recv (`mult=-1`, a read) with
`args = [address_space, pointer, b0, b1, b2, b3, timestamp]`. The `memory`
optimizer pass removes interactions; removal is sound *iff*, per alias
class, the send↔recv pairing is forced. `membus` surfaces exactly the
pieces that decide that — the recovered address **key**, the timestamp
**order**, and the **alias** structure — and, uniquely, can turn every one
of its own deductions into an independently z3-checked proof obligation.

### Subcommands

Input is resolved the same way `lens` does: `<group> <block> <step>` (e.g.
`keccak 2100224 022`), or explicit files via `--file-a`/`--file-b`.

- **`stats <group> <block> <step>`** — per-address-space shape of one
  circuit's memory bus: interaction count, send/recv balance, symbolic vs.
  concrete keys, distinct alias classes, and the two preconditions `extract`
  needs (`sends_ordered`, `recvs_bounded`). Start here.
  ```sh
  membus.py stats keccak 2100224 022
  ```
- **`info <group> <block> <step> [--as N] [--limit N] [--debug-propagate]`**
  — one row per interaction: send/recv kind, address space, recovered key
  (`const <v>`, `<base>+<off>`, or `unresolved(...)`), timestamp column with
  its position in the deduced order, and an alias-class id.
  ```sh
  membus.py info keccak 2100224 021 --as 2
  ```
- **`solve <group> <block> <step> [--as N=1] [--assume-is-valid]`** — solves
  the bus constraints (no memory-consistency assumption smuggled in) to
  recover, per cell, the recv↔send matching, and classifies each
  interaction as `input` (reads the block-entry value), `output` (escapes
  the block, read by nothing), or interior `flow` (recv `← #send`).
  Constant keys go through an exact graph algorithm; symbolic keys (AS2)
  fall back to the SMT-backed forcing check in `smtsolve.py`, with aliasing
  left open.
  ```sh
  membus.py solve keccak 2100224 022 --as 1
  ```
- **`extract <group> <block> <stepA> [stepB] [--as N] [-o FILE]`** — emits a
  `.bus` file in the `busat` textual format: each interaction's timestamp
  abstracted to a symbol `ts_i`, plus `DEFS` (recovered `base+offset` keys)
  and `CONSTRAINTS` (justified `<` order edges, each preceded by a `#`
  justification comment). One circuit dumps the whole bus; two dumps only
  the **removed** set (A − B).
  ```sh
  membus.py extract keccak 2100224 021 022 --as 2 -o as2.bus
  ```
- **`align <group> <block> <before> <after> [--as N=1]`** — the high-
  confidence before/after mapping described below.
  ```sh
  membus.py align keccak 2100224 021 022
  ```
- **`certify <group> <block> <step> [--run] [--z3-path PATH] [-o DIR]`** —
  emits (and, with `--run`, checks) one SMT certificate per fact the
  analysis extracted from that dump.
  ```sh
  membus.py certify keccak 2100224 022 --run
  ```

### `align`: mapping a removal pass

`align.compute(before, after, mem_id, addr_space)` accounts for **every**
`before` interaction one of two ways:

- **cross-match** — a kept interaction maps to its equivalent in `after`,
  matched *purely by* `(effective kind, canonical timestamp)`. This is
  explicitly a **guess**: optimizer passes rewrite pointer expressions of
  kept interactions (re-association, limb substitution) but never their
  timestamp, so the pointer is deliberately excluded from the match key. A
  wrong cross-match only costs completeness downstream (an unprovable VC),
  never soundness.
- **local connection** — from `solve(before)`: a recv paired with the local
  send it reads, or vice versa. On symbolic-key spaces only claims `solve`
  marked **forced** (true under every possible aliasing resolution) are
  ever committed.

`align` is deliberately unforgiving: it raises (CLI exit 2) rather than
emit a mapping it can't justify — `after` must be a subset of `before`, the
removed set must self-balance (nothing removed touches the boundary,
nothing kept was a removal's partner), and every match must be
unambiguous. A concrete worked example from `tests/membus/test_align.py`:
given a `before` cell with `[send_a, recv_a(input), send_b(output),
recv_b]` where `recv_b` reads `send_a`, an `after` that drops the interior
pair `(send_a, recv_b)` produces `al.n_local_pairs == 1` with
`row(0).local_partners == [3]` and `row(3).local_partners == [0]` — the
tool has independently reconstructed that those two specific interactions
were an internally-balanced write/read pair safe to elide, using nothing
but the timestamp/order facts.

### `certify`: turning every deduction into its own proof obligation

Every fact `membus` produces — a `Bound`, `Gap`, `RecvUpper`, `AffineDef`,
`EffKind`, `Pin`, `LinZero`, or `ExprEval` (see `facts.py`) — is a frozen
dataclass carrying `sources` (which raw constraint/bus-interaction indices
it came from), `premises` (other facts it was built on), and
`assumptions` (which of the three named `Assumption`s it relies on:
`TS_BOUND`, `MEMBUS_BYTE`, `ACTIVE_SELECTOR` — see below). Nothing is
trusted just because a Python function returned it.

`certify.certificate(analysis, fact)` mechanically renders one SMT-LIB
query per fact:

1. every column is declared as an `Int` constrained to `[0, p)` (the field
   residue domain, `p` = BabyBear prime);
2. each cited **source** constraint is asserted with its native semantics —
   `E ≡ 0 (mod p)` for an algebraic constraint (a product constraint splits
   into the prime-field disjunction `F1≡0 ∨ F2≡0 ∨ …`, since `p` is prime),
   a range-check bus row as `E mod p ∈ [0, 2^bits)`, gated on the row
   actually being sent (`mult ≠ 0`);
3. each cited **premise fact** is asserted as its own claim (certificates
   compose recursively along the fact DAG — a premise's own certificate is
   what actually justifies asserting it here);
4. each cited **assumption** is asserted exactly where it attaches — never
   by column name. `TS_BOUND`/`MEMBUS_BYTE` *grant* a `Bound` fact outright,
   but only at the assumption's exact licensed range (`[0, 2^29)` /
   `[0, 256)`); a `Bound` claiming anything else is left ungranted so a
   mismatch surfaces as a failing certificate instead of silently passing;
5. finally, the fact's own claim is asserted **negated**.

`(check-sat)` must return `unsat`: the sources + premises + assumptions
prove the claim, so its negation is unsatisfiable. If z3 instead says
`sat`, the model is a **concrete counterexample** showing the extraction
rule accepted something its inputs don't actually justify — "a rule bug
shows up as a SAT certificate, not a wrong answer downstream" is not a
metaphor, it's mechanically what happens. `tests/membus/test_certify.py`
demonstrates this directly: `test_bogus_fact_certificate_is_sat` fabricates
a `Gap` fact claiming a timestamp gap of `4` when the cited source
constraint actually encodes a gap of `3`, builds its certificate, and
asserts the result is `sat` — proving the harness itself can fail loudly
rather than rubber-stamp a wrong deduction. The companion
`test_certificates_are_unsat` checks every *real* fact from a realistic dump
does come back `unsat`. `certify_dump(data, run=True)` runs this over every
fact extractable from a dump in one pass; `--run` on the CLI wires this up
end to end and exits nonzero if anything comes back non-`unsat`.

The three assumptions are the *only* things taken on faith, and are
deliberately positional/structural rather than name-based: `TS_BOUND`
(any column in a memory-bus timestamp slot, or gap-linked to one, lies in
`[0, 2^29)` — true because openvm's offline memory checker enforces it, but
not itself derivable from a dump), `MEMBUS_BYTE` (a recv's data args are
bytes — reads are trusted, writes are the circuit's own proof obligation),
and `ACTIVE_SELECTOR` (`--assume-is-valid`: the one column structurally
gating every memory multiplicity in the dump is fixed to 1).

### Extraction rules (`rules.py`)

`rules.py`'s `Analysis` class is the deduction engine; its module docstring
names the rules after the R0/R1/R2 scheme of an earlier prototype. Each
rule performs its own **window argument** (bounds tight enough that a
field equation reduces to the claimed integer statement) explicitly, and
*declines* — returns nothing — rather than assume the common case when it
can't:

- **R0 → `Bound`** — a range-check bus arg bounds its value; a *scaled* arg
  `c·col` bounds `col` via the modular inverse of `c`, when that stays
  small enough to avoid wraparound. Memory-bus recv data are bytes by
  `MEMBUS_BYTE`. Bounds then propagate to a fixpoint across `pos = neg + d`
  two-column constraints.
- **Timestamp domain** — a column is a *clock* purely because it sits in a
  send's timestamp slot (never by name); linked columns (the `from_state`
  ±1 chain) join the same domain with a derived, not assumed, bound.
- **R1 → `Gap`** — a two-clock-column constraint `a − b + c = 0` reads as
  the integer gap `a = b − c`, premised on both columns' bounds fitting
  under `p`.
- **R2 → `RecvUpper`** (two forms) — a constraint form (`fs − pv − Σmᵢlᵢ + c
  = 0` with bounded limbs) and a range-check form for the post-`inlining`
  shape where the top limb survives only as a scaled range-checked
  residue — the latter enumerates the residue's integer preimages and
  requires every one to be non-negative, since accepting on sign alone
  (without checking every candidate) was a real historical soundness gap.
- **Affine gadget → `AffineDef`** — solves a byte-decomposition gadget
  `G·H=0, H=G+δ` for a limb, but only once the chosen root is proven
  unique in its window *and* the other factor's in-window roots are
  refuted (the gadget has two roots; a rule that only checks the first is
  unsound).
- **Kind → `EffKind`** — resolves a multiplicity expression to send/recv/
  disabled: constant `±1/0` always works; under `--assume-is-valid`, `±g`
  also resolves where `g` is the single column structurally gating every
  non-constant memory multiplicity in the dump.

### Supporting modules

- **`propagate.py`** — constant propagation over memory multiplicities
  (deciding-flag enumeration, capped at 2¹⁶ combinations), itself certified
  via the same `Fact` machinery (`Pin`, `LinZero`, `ExprEval`) rather than
  being a separate untrusted optimization.
- **`solve.py`** — the per-address-space matching solver described under
  `align` above: a prefix-interval graph algorithm over each key's totally-
  ordered sends, with `RecvUpper` bounds intersected across every extracted
  constraint (not just the first found) so a solution respects all of them.
- **`smtsolve.py`** — upgrades a symbolic-key (AS2) guessed claim to
  *forced* by checking, over the integers with busat MEM semantics, that
  blocking the claim is UNSAT with aliasing left fully open — i.e. it holds
  under every possible aliasing resolution, not just the no-alias reading
  `solve.py` computes by default.
- **`keys.py`** — turns certified `AffineDef` facts into `BaseOffset`
  labels (`base` = column identity of the address's low-limb decomposition,
  `offset` = the recovered constant, `mod` = usually `2^16`, the carry root
  of a 16-bit address add) — the actual "key recovery" the CLI help text
  refers to.
- **`linform.py`** — the single normalization layer every rule consumes
  expressions through: parses a dump expression into a canonical `LinForm`
  (signed residues, zero-coefficients dropped), a `Product` of two linear
  factors, or declines (`None`) — no rule ever reads raw JSON directly.
- **`order.py`** — propagates `Gap`-fact offsets into a per-connected-
  component virtual clock, conflict-checking (two disagreeing gap paths
  poison the whole component rather than silently pick one).
- **`naming.py`** — display-only column labels; explicitly documented as
  never load-bearing, since the fact layer identifies timestamps/selectors
  structurally, not by name.
- **`busfmt.py`** — renders the `busat` `.bus` text format for `extract`
  (lifting compound fields into `DEFS` lines with common-subexpression
  sharing).
- **`busmodel.py`** — the one place that knows OpenVM bus argument layouts
  (`MEMORY`=1, `VAR_RANGE`=3, `BITWISE`=6, `TUPLE_RANGE`=7) — everything
  else consumes rows through its typed `MemRow`/`range_bus_rows`, never raw
  indexing.
- **`meminfo.py`** / **`memstats.py`** — build the `info` command's per-
  interaction rows and the `stats` command's per-address-space aggregates
  (including the two extraction preconditions) respectively.
- **`extract.py`** — the abstract-timestamp `.bus` emission algorithm
  itself (distinct from `busfmt.py`'s text rendering): assigns one symbol
  per interaction's timestamp, then derives (never guesses) order edges
  between them purely from virtual-time facts.
- **`render.py`** — all human/JSON/plain-text rendering for every
  subcommand, plus the `--agent` guide text.

## The simplifier

An SMT-LIB script that's about to be handed to z3 is usually first run
through a "tactic" — a `:`-separated pipeline of named rewrite passes
(`main.py simplify <tactic> in out`, or via `orchestrate.py`'s `verify`
command automatically). `src/simplifier.py` assembles pipelines from smaller
fragments with load-bearing comments recording hard-won lessons — e.g.
`TACTIC_QEPREFIX = "nnf:skolem:lift:witness:demod:isqf"` is the quantifier
elimination sequence that reduces a soundness `ForAll` to ground form.
`STEP_TACTICS` maps optimization-step names (parsed from the input filename,
e.g. `memory`, `inlining`, `rule_based`) to pipeline overrides.

Each pass has a **Python reference implementation** under `src/simplify/`
(one module per pass — `nnf.py`, `demod.py`, `bounds.py`, `skolem*.py`,
`normalize.py`, etc., plus `src/simplify/intervals/` for interval-arithmetic
reasoning) and, for the hottest passes, a **Rust reimplementation** under
`rust/simplifier/src/passes/` for speed (`src/simplify/rust.py` resolves the
compiled binary and dispatches to it; the Python version remains the
fallback and reference implementation). `src/rewriter/` implements the
`rewrite` pass specifically, using SymPy for modular polynomial factoring.

## The checker

`main.py check` runs a script through z3 and classifies the result against
any `(set-info :status ...)` expectation. Three strategies (`--strategy`, or
per-optimization-step override via `CHECK_STRATEGIES`):

- **`plain`** (default) — solve the whole script at once. Comment-documented
  rationale: across the guest-keccak benchmark, almost every VC solves
  whole-script in seconds, while splitting the goal disjunction into
  per-disjunct solves can turn an instant solve into a slow case-split.
- **`chunked`** — the Rust checker's per-disjunct chunked mode (with a Python
  fallback).
- **`sliced`** (`src/check/sliced.py`) — for the two step names where the VC
  is a wide conjunction with a per-disjunct-easy/whole-script-hard goal
  (`inlining`, `rule_based`): escalates each disjunct through increasingly
  larger cone-of-influence slices (syntactic → arithmetic slice → memory
  slice → union → full context) with an explicit invariant that a slice is
  always a subset of the full context, so slice-UNSAT implies full-UNSAT and
  a `sat` verdict is only ever reported once validated against the whole
  context.

Retries run a small grid of solver configs (varying z3's random seeds — its
nonlinear/array tactics are seed-sensitive) before falling back to a longer
single attempt, and distinguish real timeouts from memouts via `(get-info
:reason-unknown)`.

## The Rust workspace

Three crates under `rust/`, sharing a workspace `Cargo.toml`:

| crate | binary | depends on | purpose |
|---|---|---|---|
| `smt2` | *(library only)* | `z3`, `z3-sys` | SMT-LIB parsing/pretty-printing straight into real Z3 ASTs |
| `simplifier` | `simplifier` | `smt2`, `z3`, `flint3-sys` | fast reimplementation of the hottest simplify passes |
| `checker` | `checker` | `z3`, `regex` | fast solver-invocation binary (no `smt2` dep — it only solves, doesn't round-trip) |

**`smt2` is the only crate that names `z3-sys`**, deliberately. `z3-sys` is the
raw FFI layer and `z3` the safe wrapper built on it; the two must resolve to a
single `z3-sys`, or raw pointers passed between them would be different types
from different crate instances. Confining the direct dependency to one crate
keeps that constraint in one place — `cargo tree -i z3-sys` should always show
`smt2` and `z3` as the only parents. Where another crate needs something the
safe wrapper doesn't expose, `smt2` exports a helper instead of the raw call:
`with_numeral_cstr` is the example, handing a numeral's digits to a callback as
Z3's own `CStr` so `simplifier` can feed FLINT's `fmpz_set_str` directly,
without a `String` round trip and without its own `z3-sys` dependency.

**Why `smt2` exists in-house**: it feeds SMT-LIB commands directly into real
`z3::ast` nodes via Z3's own native parser context, rather than into an
independent IR that would need a separate translation step — while *also*
being able to faithfully pretty-print scripts back to text (needed by the
simplifier's staged output). General-purpose SMT-LIB crates don't do both.
Its `ast_util.rs` also has direct compatibility shims with the Python side —
e.g. renaming Z3's internal `if` decl to SMT-LIB's `ite`, since pysmt expects
the latter.

**`simplifier`** (`rust/simplifier/src/passes/`) mirrors specific Python
passes for speed — several modules literally say "Python `X` parity" in
their doc comments (`nnf`, `normalize`, `pretty`). `poly_factor/` wraps
[FLINT](https://flintlib.org/) (via `flint3-sys`, chosen over the older
`flint-sys` specifically because it builds on macOS too) for multivariate
polynomial factorization, used by the `rewrite` pass. `skolem/` is its own
sub-module tree — skolemization is the most complex pass. Invocation:

```
simplifier [--timeout SEC] [--pretty] [--dump-steps] <input> <tactic> <output>
```

(`-` for stdin/stdout; per-step JSON stats go to stderr.)

**`checker`** runs Z3 directly, with a chunked large-disjunction mode, and
emits a generic `Action` JSON tree (`{"__Action": {name, props, actions,
running_time}}`) — the same lightweight report shape the Python side already
uses, so its output nests directly into a larger Python-side report.
Invocation:

```
checker [--dump-model PATH] [--solve-chunked] [--timeout SEC] <input.smt2>
```

**Building**: `cd rust && just build` — that is the whole thing; the recipe
sources `z3-env.sh` for you. To do it by hand, `source verifier/z3-env.sh`
first, then `cargo build --release --workspace`. Forgetting the source step
gives `ld: library 'z3' not found`, because the linker gets a bare `-lz3` with
no `-L` to resolve it.

| recipe | what |
| --- | --- |
| `just build` | all three crates, release |
| `just test` | the above plus `cargo test --workspace` |
| `just check` | type-check only, no linking — quickest way to catch a bad z3 bump |
| `just build-sandboxed [args]` | `just build` inside a `nono` sandbox |
| `just build-with <dir>` | build against some other z3 |

`build-sandboxed` exists because a hand-written `nono run -- cargo build` needs
the z3 SDK on the allow-list: it lives outside the cwd tree, so the sandbox
hides it and the link fails the same way as a missing `source`, but with an
`ld: warning: search path ... not found` line above it. The recipe derives the
path from `z3-env.sh` rather than hard-coding it.

There is no `build.rs` in this workspace. Discovery and linking are entirely
z3-sys's own build script, driven by three upstream environment variables that
`z3-env.sh` sets:

| variable | why |
| --- | --- |
| `Z3_LIBRARY_PATH_OVERRIDE` | `-L` for the workspace SDK, so `-lz3` resolves to it |
| `Z3_NO_PKG_CONFIG` | stops z3-sys probing pkg-config, which would otherwise silently prefer a system/brew z3 too old for the parser-context API `smt2/z3_parse.rs` needs |
| `Z3_SYS_Z3_VERSION` | states the version rather than letting z3-sys guess; with pkg-config off it has no other way to detect one |

plus an rpath in `RUSTFLAGS` so the built binaries find `libz3` at runtime
without `LD_LIBRARY_PATH` — which is deliberately avoided, since it would also
apply to `python3` and hijack the `z3-solver` package's own bundled `libz3`.

To build against a different z3 — a local checkout, say — use `just build-with
<dir>`, or set the same variables yourself. To move the whole workspace to
another release, change `Z3_VERSION` in `verifier/z3-env.sh`: `setup.sh` and CI
read it from there, and the Python solver registry picks up whatever ends up in
`z3/bin/` by filename, so no other file names a version.

On macOS, `flint3-sys` builds FLINT from source and needs autotools (`autoconf
automake libtool`, plus `m4`) — `just build-with <z3dir>` checks for these and
gives you the `brew install` command if missing (the same set `setup.sh`
checks for). The toolchain is pinned via `rust-toolchain.toml`
(`min-version = "1.85"`; CI additionally pins an exact `1.95.0` for
build-cache-fingerprint stability across jobs).

## Reporting, inspection and debugging tools

- **`src/report/`** — `action.py`'s `Action` is the hierarchical
  timing/result record used throughout the pipeline
  (`with Action("encode") as a: a += {...}`); `database.py` persists these
  into SQLite (`report-<name>.db` at repo root); `plots.py` builds the actual
  charts (solve-percentage ECDFs, time-vs-size scatter, per-pass stats);
  `render.py` assembles it all into the static `report-<name>.html` files.
  Generate one with `main.py report <reports-dir> <output>.html`.
- **`src/visualizer.py`** (`main.py visualize`) — colorized terminal
  visualization of bus contents over time under a model; currently only
  understands the `memory` and `execution bridge` buses.
- **`src/diff.py`** (`main.py diff`) — opens two formatted dump renderings
  side-by-side in `meld`.
- **`src/evaluator.py`** (`main.py eval`) / **`evaluate.py`** (standalone) —
  "show me exactly which constraint/consequence/axiom this model violates."
  `evaluate.py` is a separate standalone re-implementation used directly by
  `orchestrate.py evaluate` (as opposed to `main.py eval`, used by
  `orchestrate.py eval`).
- **`lens.py`** / **`src/lens/`** — a standalone statistics/inspection CLI
  over the raw APC dump trail: `lens.py show|sweep|diff|subs|compare`, e.g.
  `lens.py sweep all keccak --sort consF` to find the least-optimized
  blocks, or `lens.py diff keccak <block> 010 011` to see exactly what one
  pass changed. Can join against a report DB to annotate dumps with solve
  time/status. Run `lens.py --agent` for a dense machine-readable guide.
- **`membus.py`** / **`src/membus/`** — a standalone CLI for diagnosing the
  memory bus specifically (key recovery, alignment across a removal pass,
  certified proof obligations for every deduction) — see
  [`membus`](#membus--memory-bus-diagnosis-alignment-and-certified-extraction)
  above.
- **`src/verify/bug_injection.py`** (`--inject [seed]` on `verify`/`diff`) —
  nine deterministic mutation operators (drop/modify a constraint, drop/modify
  a bus interaction, drop/swap an instruction, drop a derived column) used to
  confirm the verifier actually rejects a broken circuit — the soundness-side
  complement to the ordinary correctness test suite.
- **`src/encoding_analysis.py`** (`main.py aliasing`) — diagnostic: enumerates
  which memory-pointer alias relations are consistent with a dump's
  constraints, by repeatedly asking the solver for a model and blocking it.

## Testing

`uv run pytest` from the repo root runs everything (`pyproject.toml` sets
`pythonpath = ["."]` so `from src.foo import bar` resolves without
installing the package). Two kinds of tests:

**Unit tests** under `tests/`, mirroring `src/`'s layout
(`tests/simplify/`, `tests/membus/`, `tests/lens/`, `tests/check/`,
`tests/bus_interactions/`, `tests/verify/`, `tests/report/`,
`tests/rewriter/`, `tests/utils/`, `tests/misc/`). Style varies by area:
`tests/simplify/` builds formulas directly via the pysmt API or parses
hand-written SMT-LIB2 fixtures and asserts on pass output; most files that
touch pysmt declare a local `push_env()`/`pop_env()` fixture (there's no
shared `conftest.py`) because pysmt keeps one global symbol table and a
symbol redeclared with a different sort in an earlier test breaks later
ones.

**Declarative end-to-end regressions** under `tests/regression_cases/`,
driven by `tests/regressions.py`. Each subdirectory has a `case.toml`:

- `[case]` — `tags`, `description` (often a detailed soundness-bug
  post-mortem), `requires` (`"powdr"` skips unless the sibling checkout
  exists; `"rust-simplifier"`/`"rust-checker"` skip unless those binaries are
  built).
- `[source]` (optional) — provenance for regenerating fixtures from a live
  `powdr-dumps/` directory.
- `[inputs]` — named fixture files (or a whole staged `powdr-dumps/` subtree).
- `[[steps]]` — one or more `{script, args, timeout}` runs of `main.py` or
  `orchestrate.py`, with `{placeholder}` substitution.
- `[[assert]]` — checked against the immediately preceding step
  (`exit_ok`, `check_result`, `pass_stats`/`pass_unchanged`, `isqf`,
  `json_path`, `file_equals`, `json_file_equals`).

Cases are picked up automatically by plain `pytest` (one `test_<name>`
function is generated per case at import time) — no special invocation
needed. `REGRESSION_TAGS=tag1,tag2` filters to matching cases;
`REGRESSION_UPDATE=1` turns golden-file assertions into writers (use after an
intentional behavior change). Add a new case with:

```sh
uv run python3 tests/regression_cases/scaffold.py --name <name> --tags a,b \
    --from <src_dir> --files "*.json" \
    --template simplify-pass|verify-pipeline|orchestrate-verify
```

then fill in the description/steps/asserts by hand.

`uv run ruff format --diff .` / `uv run ruff check .` cover formatting/lint (config in
`pyproject.toml`: wildcard-import warnings are globally disabled since
`from ..smt.utils import *` is a deliberate house style; `src/smt_backends/
pysmt.py` and `test_*.py` files are excluded from lint).

## CI

Single workflow, `.github/workflows/verify.yaml` ("Generate rust cache for PR
builds"), on every push, four jobs:

- **`binaries`** (ubuntu + macos) — downloads/installs the z3 SDK into the
  workspace's `z3/` via `download_z3.py`, which on macOS also rewrites the
  downloaded `libz3.dylib`'s install-name to `@rpath/libz3.dylib` (bare
  install-names aren't resolved via `LC_RPATH`). The cache key includes
  `z3-env.sh`, so bumping the pin invalidates it.
- **`build-rust`** (needs `binaries`; ubuntu + macos) — pins the Rust
  toolchain to `1.95.0` and runs `cargo build --release --workspace` +
  `cargo test --release --workspace`, purely to warm the shared build cache
  before `lint`/`build` need the same artifacts.
- **`lint`** (needs `binaries`, `build-rust`; ubuntu only) — `ruff
  format --diff`, `ruff check`, `pytest`, all with `continue-on-error: true`
  (visible in logs, doesn't fail the job).
- **`build`** (needs `binaries`, `build-rust`; matrix
  `{ubuntu: single_add_1 single_loadbu, macos: single_add_1}`) — the real
  end-to-end job. Checks out this repo under `path: verifier` **and**
  `powdr-labs/powdr` under `path: powdr`, then for each test case runs the
  full `orchestrate.py` pipeline (`powdr` → `trace` → `eval` → `evaluate` →
  `verify`) and uploads the generated HTML report as a build artifact.
  macOS only runs the smaller test case, most likely a runner-cost/time
  tradeoff (not stated explicitly in the workflow).

Caching: `bin-sdk-<os>-<hash>` (z3 SDK, per-OS), `verifier-rust-<os>-<hash>`
(this repo's `rust/target/` **and** `~/.cargo/registry`+`~/.cargo/git`
together — both are needed, or every job re-extracts crate sources with
fresh mtimes and Cargo treats the whole dependency tree as stale despite a
`target/` cache hit; the key includes a hash of the workflow file itself so
a caching-behavior change invalidates old incompatible cache entries instead
of restoring them forever), and a separate `cargo-<hash>-<date>` cache for
the sibling `powdr/` checkout's own independent `Cargo.lock`.

## Utility script reference

| script | for |
|---|---|
| `evaluate.py` | manually check a solver model is real, given a dump + model JSON |
| `download_z3.py` | fetch a prebuilt z3 SDK/binary for the current OS/arch |
| `benchmark_solvers.py` | run a batch of solver configs over a directory of `.rewrite.smt2` files, resumable |
| `plot_benchmark_results.py` | plot `benchmark_solvers.py` output (needs the `plots` extra: `uv sync --extra plots`) |
| `select_blocks.py` | cut a large `powdr-dumps/` dir down to the top-N most-optimized blocks |
| `simplify_smt2.py` | cheap regex-based textual `.smt2` cleanup (not the real simplifier) |
| `find_duplicated_ids.py` | one-off check that powdr never reuses a variable id across programs |
| `check-pp-pipeline.py` | personal debugging scratch script (hardcoded paths, `meld`-based); not a general tool |
| `lens.py` / `membus.py` | wrappers for the `src/lens`/`src/membus` inspection CLIs — see above |
| `setup.sh` | provision a regular workstation (checks deps, never sudo-installs) |
| `ec2-setup.sh` | provision a throwaway box (installs everything automatically) |
| `z3-env.sh` | `source` before building/running anything that links z3 |
| `ec2-run.sh <scenario> [verify-args...]` | repeat a full benchmark run (`keccak`, `keccak-selection`, `pairing`, `reth`) on an already-provisioned box |
| `ec2-sync.sh <scenario>` | rsync dumps/reports back from a remote benchmark box and regenerate its HTML report |

## Known rough edges

- `tests/regression_cases/inlining-replay/case.toml` still invokes
  `main.py powdr-opt ...`, a subcommand that was removed when the
  `powdr_opt` feature was deleted from this repo. It's gated by
  `requires = ["powdr"]` so it silently no-ops without a sibling `powdr/`
  checkout, but will error wherever one is present. Needs deleting or
  rewriting.
- `check-pp-pipeline.py` is a personal debugging scratchpad with hardcoded
  filenames and a `meld` dependency — not part of any documented workflow.
