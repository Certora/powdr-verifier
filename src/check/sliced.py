"""Sliced disjunct checking: refute each goal disjunct against a
boundary-stopped cone-of-influence slice of the context.

The VC has the shape ``ctx ∧ (d_0 ∨ ... ∨ d_n)`` with ``ctx`` in the tens of
thousands of conjuncts. Solving each ``ctx ∧ d_k`` against the FULL context
couples the arithmetic and memory-permutation arguments and times out on the
largest blocks; each argument alone is fast. Per disjunct we therefore solve
the smallest sufficient slice and escalate only when forced:

    0. verdict cache (an identical disjunct was already refuted)
    1. syntactic: ``d.simplify()`` is false
    A. non-empty slice: boundary-stopped COI of d's free vars   (arith rung)
    M. empty slice: the shared "memory argument" (all constraints
       touching a boundary variable)                            (mem rung)
    E. slice ∪ memory argument                                  (escalated)
    F. the full context                                         (full rung)

Soundness invariants (do not weaken):
  * every slice is a subset of ``ctx``, so slice-UNSAT ⟹ ``ctx ∧ d`` unsat;
  * slice-SAT proves nothing -- it triggers CEGAR/escalation, never a verdict;
  * "sat" is reported only for a model validated against ALL of ``ctx``
    (every conjunct partially evaluates to true, or the full-context rung
    itself returned sat);
  * "unsat" is reported only when every disjunct was refuted (explicit count);
  * learned ``Not(d)`` and CEGAR-added constraints are ctx members or
    ctx-consequences, preserving both directions.

The script's declarations are not replayed: the patched
``SmtLibSolver.add_assertion`` auto-declares free variables.
"""
import json
import logging
import re
import statistics
import subprocess
import tempfile
import time
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

from ..report.action import Action
from ..smt.utils import *
from ..utils.args import ARGS
from .coi import ConstraintIndex, boundary_vars

DEFAULT_BOUNDARY_REGEX = r"memory_(match|isinput|isoutput|isdisabled)"
# Retry tactic for disjuncts the incremental core cannot decide: push/pop
# solving bypasses z3's tactic-level preprocessing, and on the TS_BOUND
# obligation family the solve-eqs/propagate-values pipeline collapses the
# mod-chain equalities that otherwise drown the simplex tableau (measured:
# plain incremental unknown at 900s -> unsat in ~13s with this tactic).
# MUST run one-shot (subprocess on a serialized query): under an open push
# scope z3 weakens the tactic (solve-eqs cannot eliminate variables) and the
# same query times out (13s one-shot vs 90s+ under push -- measured).
DEFAULT_RETRY_TACTIC = "(then simplify propagate-values solve-eqs smt)"
_HARD_DISJUNCTS_CAP = 100


@dataclass
class SliceBudgets:
    """Per-rung z3 budgets (ms) and CEGAR limits."""

    arith_ms: int = 20_000
    mem_ms: int = 40_000
    full_ms: int = 60_000
    cegar_iters: int = 3
    cegar_batch: int = 64
    # Escalation policy: slices up to this size escalate by pushing the
    # slice into a scope of the shared memory-argument solver; larger ones
    # go straight to the full-context solver (pushing ~13k constraints per
    # escalation would be prohibitive).
    small_slice: int = 500
    # The growing slice solver is GC'd (restarted) when its resident context
    # exceeds this factor x the current query's slice size. Batches are
    # processed in ascending slice-size order, so with near-identical big
    # slices the context grows once and GC never fires.
    gc_factor: float = 4.0
    # Budget for the one-shot tactic retry subprocess.
    tactic_ms: int = 60_000
    # Budget for the one-shot closed-slice subprocess. Measured on the
    # TS_BOUND family: 0.01-0.5s at ~426 constraints (2102932, one mod!
    # witness) but ~33s at ~2289 constraints (2100224, a 4-deep stacked
    # witness chain) -- the budget must cover the deep-chain shape.
    closed_ms: int = 60_000

    @classmethod
    def from_args(cls) -> "SliceBudgets":
        a = ARGS()

        def sec(name, default):
            return int(float(getattr(a, name, default) or default) * 1000)

        return cls(
            arith_ms=sec("sliced_arith_timeout", 20.0),
            mem_ms=sec("sliced_mem_timeout", 40.0),
            full_ms=sec("sliced_full_timeout", 60.0),
            cegar_iters=int(getattr(a, "sliced_cegar_iters", 3) or 3),
            small_slice=int(getattr(a, "sliced_small_slice", 500) or 500),
            gc_factor=float(getattr(a, "sliced_gc_factor", 4.0) or 4.0),
            tactic_ms=sec("sliced_tactic_timeout", 60.0),
            closed_ms=sec("sliced_closed_timeout", 10.0),
        )


class Metrics:
    """Timers, counters, and value distributions for the run report.

    Everything lands in the Action JSON so a slow or surprising run is
    diagnosable from the report alone, without a re-run.
    """

    def __init__(self):
        self._times: dict[str, list] = {}  # name -> [total_s, count, max_s]
        self.counters: defaultdict = defaultdict(int)
        self._samples: defaultdict = defaultdict(list)

    @contextmanager
    def timed(self, name: str):
        t0 = time.perf_counter()
        try:
            yield
        finally:
            self.add_time(name, time.perf_counter() - t0)

    def add_time(self, name: str, dt: float):
        rec = self._times.setdefault(name, [0.0, 0, 0.0])
        rec[0] += dt
        rec[1] += 1
        rec[2] = max(rec[2], dt)

    def count(self, name: str, n: int = 1):
        self.counters[name] += n

    def sample(self, name: str, value):
        self._samples[name].append(value)

    def as_dict(self) -> dict:
        return {
            "timing_s": {
                k: {"total": round(v[0], 4), "count": v[1], "max": round(v[2], 4)}
                for k, v in sorted(self._times.items())
            },
            "counters": dict(sorted(self.counters.items())),
            "distributions": {
                k: {
                    "min": min(v),
                    "median": statistics.median(v),
                    "max": max(v),
                    "count": len(v),
                }
                for k, v in sorted(self._samples.items())
                if v
            },
        }

    def summary_lines(self) -> list[str]:
        d = self.as_dict()
        lines = ["sliced-check metrics:"]
        for k, v in d["timing_s"].items():
            lines.append(f"  time {k}: total={v['total']}s n={v['count']} max={v['max']}s")
        for k, v in d["counters"].items():
            lines.append(f"  count {k}: {v}")
        for k, v in d["distributions"].items():
            lines.append(
                f"  dist {k}: min={v['min']} median={v['median']} max={v['max']} n={v['count']}"
            )
        return lines


def _parse_value(text: str) -> FNode | None:
    """A scalar model value from a ``get-value`` response: Bool, Int, or
    negated Int. Anything else (arrays, UFs) returns ``None`` and is skipped."""
    text = text.strip()
    if text == "true":
        return TRUE()
    if text == "false":
        return FALSE()
    m = re.fullmatch(r"\(\s*-\s+(\d+)\s*\)", text)
    if m:
        return Int(-int(m.group(1)))
    if re.fullmatch(r"-?\d+", text):
        return Int(int(text))
    return None


def _abstract_mods(formulas: list[FNode]) -> tuple[list[FNode], list[FNode]]:
    """Rewrite every ``(mod a b)`` into an application of an uninterpreted
    ``umod!abs`` and return quotient-free axioms for each application with a
    positive constant divisor: range ``0 <= umod(a,b) < b`` and no-wrap
    ``0 <= a < b -> umod(a,b) = a``.

    Refutation-sound over-approximation: both axioms are true of real mod
    (for b > 0), so every model of the original satisfies the abstraction --
    unsat transfers, sat is inconclusive. The point is to keep z3's arith
    solver away from quotient case-splitting: on the TS_BOUND obligation
    closed slices this is 87.6s (default, interpreted) / 3.4s (arith2) ->
    **0.5s** (default, abstracted). Pure EUF opacity WITHOUT the axioms is
    too weak (measured sat)."""
    umod = Symbol("umod!abs", FunctionType(INT, [INT, INT]))
    mgr = get_env().formula_manager
    memo: dict[FNode, FNode] = {}

    def rewrite(root: FNode) -> FNode:
        stack = [root]
        while stack:
            n = stack[-1]
            if n in memo:
                stack.pop()
                continue
            pending = [a for a in n.args() if a not in memo]
            if pending:
                stack.extend(pending)
                continue
            args = tuple(memo[a] for a in n.args())
            if n.node_type() == operators.MOD:
                memo[n] = Function(umod, list(args))
            elif not n.args() or args == tuple(n.args()):
                memo[n] = n
            else:
                memo[n] = mgr.create_node(
                    node_type=n.node_type(), args=args, payload=n._content.payload
                )
            stack.pop()
        return memo[root]

    rewritten = [rewrite(f) for f in formulas]
    apps = sorted(
        (
            n
            for f in rewritten
            for n in iter_unique_subnodes(f)
            if n.is_function_application() and n.function_name() == umod
            and n.arg(1).is_int_constant() and n.arg(1).constant_value() > 0
        ),
        key=lambda n: n.size(),
    )
    return rewritten, apps


def _mod_axioms(u: FNode) -> list[FNode]:
    """The quotient-free axiom instances for one ``umod!abs`` application."""
    a, b = u.arg(0), u.arg(1)
    return [
        And(LE(Int(0), u), LT(u, b)),
        Implies(And(LE(Int(0), a), LT(a, b)), Equals(u, a)),
    ]


_GET_VALUE_PAIR = re.compile(r"\((?:appv|argv)!(\d+)\s+(?:\(-\s*(\d+)\)|(-?\d+))\)")


def _violated_apps(apps: list[FNode], stdout: str) -> list[FNode] | None:
    """Which applications' axioms does the model falsify?

    The query names each application's value ``appv!i`` and its argument's
    value ``argv!i``; the get-value response is regex-parsed. Returns None
    if the response is unusable."""
    values: dict[tuple[str, int], int] = {}
    for m in _GET_VALUE_PAIR.finditer(stdout):
        idx = int(m.group(1))
        val = -int(m.group(2)) if m.group(2) is not None else int(m.group(3))
        kind = "appv" if m.group(0).startswith("(appv") else "argv"
        values[(kind, idx)] = val
    violated = []
    for i, u in enumerate(apps):
        uv = values.get(("appv", i))
        av = values.get(("argv", i))
        if uv is None or av is None:
            return None
        bv = u.arg(1).constant_value()
        if not (0 <= uv < bv) or (0 <= av < bv and uv != av):
            violated.append(u)
    return violated


def _declare_line(v: FNode) -> str:
    """A ``declare-fun`` for a symbol, handling uninterpreted FUNCTIONS
    (e.g. ``uf_and : Int Int -> Int``) as well as plain constants --
    ``get_free_variables`` yields both."""
    t = v.symbol_type()
    if t.is_function_type():
        params = " ".join(_smt_type(p) for p in t.param_types)
        return f"(declare-fun {quote(v.symbol_name())} ({params}) {_smt_type(t.return_type)})"
    return f"(declare-fun {quote(v.symbol_name())} () {_smt_type(t)})"


def _write_query(path, formulas: list[FNode], check_line: str, comment: str = "",
                 probes: list[tuple[str, FNode]] | None = None):
    """Serialize a standalone SMT2 query: declares + asserts + check line.

    ``probes`` are (name, term) pairs: each gets a fresh Int constant pinned
    to the term, and a ``(get-value ...)`` over the names follows the check
    line — a compact way to read model values of large terms back out."""
    decls = sorted(
        {v for f in formulas for v in f.get_free_variables()}
        | ({v for _, t in probes for v in t.get_free_variables()} if probes else set()),
        key=lambda v: v.symbol_name(),
    )
    with open(path, "w") as out:
        out.write("(set-logic ALL)\n")
        if probes:
            out.write("(set-option :produce-models true)\n")
        if comment:
            out.write(f"; {comment}\n")
        for v in decls:
            out.write(_declare_line(v) + "\n")
        if probes:
            for name, _ in probes:
                out.write(f"(declare-fun {name} () Int)\n")
            for name, t in probes:
                out.write(f"(assert (= {name} {t.to_smtlib(daggify=True)}))\n")
        for f in formulas:
            out.write(f"(assert {f.to_smtlib(daggify=True)})\n")
        out.write(check_line + "\n")
        if probes:
            out.write(f"(get-value ({' '.join(name for name, _ in probes)}))\n")


def _extract_model(s) -> list[tuple[FNode, FNode]]:
    """Stream-safe model extraction for the SMT-LIB pipe solver.

    ``SmtLibSolver.get_model`` has two problems here: it only covers the
    innermost push-scope's declared variables (slice variables are declared
    at the base level), and it parses ``get-value`` responses with the
    SmtLibParser whose tokenizer reads AHEAD of the response -- desyncing
    the success-acknowledgement protocol so the next command (e.g. ``pop``)
    sees an empty line. Here we issue one ``(get-value (v))`` per declared
    variable across ALL scopes and read exactly one paren-balanced response
    each, parsing scalars with a regex.
    """
    if not hasattr(s, "solver_stdin") or not hasattr(s, "declared_vars"):
        return [(k, v) for k, v in s.get_model()]
    model: list[tuple[FNode, FNode]] = []
    for scope in s.declared_vars:
        for v in scope:
            if not v.is_symbol():
                continue
            name = quote(v.symbol_name())
            s.solver_stdin.write(f"(get-value ({name}))\n")
            s.solver_stdin.flush()
            response = s.solver_stdout.readline()
            while response.count("(") > response.count(")"):
                line = s.solver_stdout.readline()
                if not line:
                    break
                response += line
            response = response.strip()
            # response shape: ((<name> <value>))
            if not (response.startswith("((") and response.endswith("))")):
                continue
            body = response[2:-2].strip()
            if body.startswith("|"):
                end = body.index("|", 1) + 1
            else:
                end = body.index(" ") if " " in body else len(body)
            value = _parse_value(body[end:])
            if value is not None:
                model.append((v, value))
    return model


class _Kind(Enum):
    REFUTED = "refuted"
    SAT_CANDIDATE = "sat-candidate"  # slice-level sat; NEVER a verdict
    SAT_VALIDATED = "sat-validated"  # model validated against the full ctx
    UNKNOWN = "unknown"


@dataclass
class _Outcome:
    kind: _Kind
    model: list | None = None  # [(symbol, value FNode)] for SAT_VALIDATED
    reason: str | None = None  # for UNKNOWN
    via_cegar: bool = False
    via: str | None = None  # winning fallback strategy: "closed" | "tactic"


def flatten_script_conjuncts(smt_script) -> tuple[list[FNode], FNode | None]:
    """All assert bodies flattened through ``And`` into a deduped conjunct
    list; the largest ``Or`` conjunct (>= 2 disjuncts) is the goal.

    Returns ``(ctx_without_goal, goal)``; ``goal`` is ``None`` when nothing
    is splittable.
    """
    conjuncts: list[FNode] = []
    seen: set[FNode] = set()
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        stack = [cmd.args[0]]
        while stack:
            f = stack.pop()
            if f.is_and():
                stack.extend(reversed(f.args()))
            elif f not in seen:
                seen.add(f)
                conjuncts.append(f)
    goal = None
    n_disjuncts = 0
    for f in conjuncts:
        if f.is_or() and len(f.args()) > n_disjuncts:
            goal, n_disjuncts = f, len(f.args())
    if goal is None or n_disjuncts < 2:
        return conjuncts, None
    return [f for f in conjuncts if f is not goal], goal


def _smt_type(t) -> str:
    """SMT-LIB rendering of a pysmt type (Int/Bool/Real/Array, recursively)."""
    if t.is_int_type():
        return "Int"
    if t.is_bool_type():
        return "Bool"
    if t.is_real_type():
        return "Real"
    if t.is_array_type():
        return f"(Array {_smt_type(t.index_type)} {_smt_type(t.elem_type)})"
    return str(t)


class _SliceDumper:
    """Serialize solver queries as standalone re-runnable SMT2 files.

    The incremental solvers make failures hard to reproduce; every
    diagnostically interesting query (anything that was not an instant
    slice-unsat, or everything with ``dump_all``) is written as
    ``d<k>_<rung>[_cegar<i>].smt2`` -- declarations + asserts + check-sat --
    plus a ``manifest.json`` keyed by disjunct index.
    """

    def __init__(self, dump_dir: Path, dump_all: bool):
        self.dump_dir = dump_dir
        self.dump_all = dump_all
        self.records: list[dict] = []
        dump_dir.mkdir(parents=True, exist_ok=True)

    def dump(self, *, k: int, rung: str, formulas: list[FNode], result: str,
             time_s: float, slice_size: int, cegar_round: int | None = None,
             interesting: bool = True):
        if not (self.dump_all or interesting):
            return
        suffix = f"_cegar{cegar_round}" if cegar_round is not None else ""
        name = f"d{k}_{rung}{suffix}.smt2"
        _write_query(
            self.dump_dir / name,
            formulas,
            "(check-sat)",
            comment=f"disjunct {k}, rung {rung}, result {result}, {time_s:.3f}s",
        )
        self.records.append(
            {
                "disjunct": k,
                "file": name,
                "rung": rung,
                "cegar_round": cegar_round,
                "slice_size": slice_size,
                "result": result,
                "time_s": round(time_s, 4),
            }
        )

    def finalize(self):
        with open(self.dump_dir / "manifest.json", "w") as out:
            json.dump(self.records, out, indent=2)


def _structure_key(d: FNode) -> tuple[str, ...] | None:
    """Cheap structural class of a disjunct, for strategy routing.

    Slow disjuncts are not the big ones — they are the structurally severed
    ones (measured on 2100224: 6/530 overlap between the 530 slowest and 530
    largest): refutations that need facts outside the arith slice, signalled
    by uninterpreted bitwise/mod applications, especially with COMPOSITE
    arguments (demod's ``+P*mod!`` witnesses inside uf args defeat
    congruence). Returns a marker tuple, or ``None`` for plain arithmetic
    disjuncts (never routed).

    Markers: ``ufc`` — uf/umod application with a composite (non-symbol,
    non-constant) argument; ``uf`` — any uf/umod application; ``modw`` — a
    ``mod!`` quotient-witness variable occurs.
    """
    markers: set[str] = set()
    stack = [d]
    seen: set[int] = set()
    while stack:
        f = stack.pop()
        if id(f) in seen:
            continue
        seen.add(id(f))
        if f.is_function_application():
            name = f.function_name().symbol_name()
            if name.startswith("uf_") or name.startswith("umod"):
                markers.add("uf")
                if any(
                    not (a.is_symbol() or a.is_int_constant()) for a in f.args()
                ):
                    markers.add("ufc")
        elif f.is_symbol() and f.symbol_name().startswith("mod!"):
            markers.add("modw")
        stack.extend(f.args())
    return tuple(sorted(markers)) if markers else None


class _ClassRouter:
    """Structure-keyed strategy preference table (learning, self-disabling).

    Generalizes the neighbor preempt: when a fallback strategy refutes a
    disjunct, remember it per structure class; later members of the class run
    that strategy FIRST, skipping the primary-rung timeout (the dominant cost
    of hard families: ~5s toll per member). Routing only starts after a real
    win, and a class whose routed attempts keep losing to the primary rung is
    disabled — the measured failure mode of a stale preempt (easy disjuncts
    paying a one-shot subprocess each) stays bounded.
    """

    DISABLE_MIN_MISSES = 8

    def __init__(self, metrics: Metrics):
        self.metrics = metrics
        self.pref: dict[tuple, str] = {}
        self.hits: defaultdict = defaultdict(int)
        self.misses: defaultdict = defaultdict(int)
        self.disabled: set[tuple] = set()

    def route(self, key: tuple | None) -> str | None:
        if key is None or key in self.disabled:
            return None
        return self.pref.get(key)

    def learn(self, key: tuple | None, via: str | None, *, routed: bool, hit: bool) -> None:
        if key is None:
            return
        if via:
            self.pref[key] = via
        if not routed:
            return
        if hit:
            self.hits[key] += 1
            self.metrics.count("class_route_hit")
            return
        self.misses[key] += 1
        self.metrics.count("class_route_miss")
        if (
            self.misses[key] >= self.DISABLE_MIN_MISSES
            and self.misses[key] > 2 * self.hits[key]
        ):
            self.disabled.add(key)
            self.metrics.count("class_route_disabled")
            logging.info("class routing disabled for %s (misses dominate)", key)


class _SlicedChecker:
    def __init__(
        self,
        ctx: list[FNode],
        goal: FNode,
        *,
        budgets: SliceBudgets,
        boundary_pattern: re.Pattern,
        metrics: Metrics,
        dumper: _SliceDumper | None,
        collect_unknowns: int | None,
        debug: bool,
        retry_tactic: str | None = DEFAULT_RETRY_TACTIC,
    ):
        self.ctx = ctx
        self.goal = goal
        self.disjuncts = list(goal.args())
        self.budgets = budgets
        self.metrics = metrics
        self.dumper = dumper
        self.collect_unknowns = collect_unknowns
        self.debug = debug
        self.retry_tactic = retry_tactic or None
        with metrics.timed("index_build"):
            boundary = boundary_vars(ctx, boundary_pattern) | frozenset(
                v for v in goal.get_free_variables() if boundary_pattern.search(v.symbol_name())
            )
            self.index = ConstraintIndex(ctx, frozenset(boundary))
        self.slice_cache: dict[frozenset, frozenset[int]] = {}
        self.closed_cache: dict[frozenset, frozenset[int]] = {}
        self.refuted: set[FNode] = set()  # verdict cache: refutations ONLY
        self.tiers: defaultdict = defaultdict(int)
        self.hard_disjuncts: list[int] = []
        self.unknown_disjuncts: list[dict] = []
        self.disjunct_rows: list[dict] = []  # debug mode only
        self._live_solvers: list = []
        self._mem_solver = None
        self._full_solver = None
        self._all_indices = frozenset(range(len(ctx)))
        # The growing slice solver: resident ctx indices asserted at its base
        # level. Grows monotonically (delta asserts); GC'd when pollution
        # exceeds gc_factor x the current query's slice.
        self._grow_solver = None
        self._grow_resident: set[int] = set()
        self._scratch_tmp = tempfile.TemporaryDirectory(prefix="sliced-tactic-")
        self._scratch = Path(self._scratch_tmp.name)
        self.router = (
            _ClassRouter(metrics) if ARGS().sliced_class_routing else None
        )

    # ---------------- solver management ----------------

    def _new_solver(self, timeout_ms: int):
        with self.metrics.timed("solver_create"):
            s = Solver(
                name=ARGS().solver,
                logic=ALL,
                incremental=True,
                solver_options={
                    "timeout": timeout_ms,
                    "smt.random_seed": 0,
                    "sat.random_seed": 0,
                },
            )
        self.metrics.count("solvers_created")
        self._live_solvers.append(s)
        return s

    def _exit_solver(self, s):
        if s in self._live_solvers:
            self._live_solvers.remove(s)
        try:
            s.exit()
        except Exception:
            pass

    def _assert_all(self, s, indices, timer: str):
        with self.metrics.timed(timer):
            for i in sorted(indices):
                s.add_assertion(self.ctx[i])

    def mem_solver(self):
        if self._mem_solver is None:
            self._mem_solver = self._new_solver(self.budgets.mem_ms)
            self._assert_all(self._mem_solver, self.index.mem_indices, "assert_replay_mem")
        return self._mem_solver

    def grow_solver_for(self, slice_idx: frozenset):
        """The growing slice solver, guaranteed to contain ``slice_idx``.

        Amortizes assertion cost across near-identical slices (Arie's
        grow+GC architecture): only the missing delta is asserted; when the
        resident context exceeds ``gc_factor`` x the current slice, the
        solver is garbage-collected (restarted) and repopulated with just
        this slice. Sound: the resident set is always a subset of ctx, so
        unsat verdicts remain proofs; pollution only costs solver effort.

        Returns ``(solver, considered)`` where ``considered`` is the
        resident index set after the delta."""
        need = len(slice_idx)
        resident = self._grow_resident
        if self._grow_solver is not None:
            grown = len(resident | slice_idx)
            if grown > self.budgets.gc_factor * need:
                self.metrics.count("grow_gc_restarts")
                self._exit_solver(self._grow_solver)
                self._grow_solver = None
                resident.clear()
        if self._grow_solver is None:
            self._grow_solver = self._new_solver(self.budgets.arith_ms)
        delta = slice_idx - resident
        if delta:
            self.metrics.count("grow_delta_asserted", len(delta))
            self._assert_all(self._grow_solver, delta, "assert_replay_arith")
            resident |= delta
        return self._grow_solver, frozenset(resident)

    def full_solver(self):
        if self._full_solver is None:
            self._full_solver = self._new_solver(self.budgets.full_ms)
            self._assert_all(self._full_solver, self._all_indices, "assert_replay_full")
        return self._full_solver

    def close(self):
        for s in list(self._live_solvers):
            self._exit_solver(s)
        if self.dumper is not None:
            self.dumper.finalize()
        self._scratch_tmp.cleanup()

    # ---------------- per-disjunct ladder ----------------

    def _slice_for(self, key: frozenset) -> frozenset[int]:
        cached = self.slice_cache.get(key)
        if cached is not None:
            self.metrics.count("slice_cache_hits")
            return cached
        with self.metrics.timed("slice_fixpoint"):
            sl = self.index.slice_indices(key)
        self.slice_cache[key] = sl
        self.metrics.count("slice_cache_misses")
        self.metrics.sample("slice_size", len(sl))
        return sl

    def _closed_slice(self, d: FNode) -> frozenset[int]:
        """The "closed slice" of ``d``: ctx constraints ALL of whose free vars
        lie in vars(d) ∪ {internal witness vars (mod!/div!/...) co-occurring
        with vars(d)}. For bound-obligation disjuncts (e.g. the TS_BOUND
        family) the refutation is interval propagation over this tiny set --
        measured 4-fact unsat cores, 0.01-0.5s with plain z3, where the full
        COI slice takes z3 85s+ to find the same proof."""
        dvars = frozenset(d.get_free_variables())
        key = dvars
        cached = self.closed_cache.get(key)
        if cached is not None:
            return cached
        with self.metrics.timed("closed_slice_build"):
            witnesses: set[FNode] = set()
            candidates: set[int] = set()
            for v in dvars:
                candidates.update(self.index.var2c.get(v, ()))
            for i in candidates:
                witnesses.update(
                    w for w in self.index.free_vars[i] if "!" in w.symbol_name()
                )
            allowed = dvars | witnesses
            for v in witnesses:
                candidates.update(self.index.var2c.get(v, ()))
            sel = frozenset(
                i for i in candidates if self.index.free_vars[i] <= allowed
            )
        self.closed_cache[key] = sel
        self.metrics.sample("closed_slice_size", len(sel))
        return sel

    def _oneshot(self, k: int, rung: str, formulas: list[FNode], *,
                 label: str, budget_ms: int, tactic: str | None = None,
                 z3_args: list[str] | None = None, slice_size: int = 0,
                 probes: list[tuple[str, FNode]] | None = None,
                 ) -> tuple[bool | None, str]:
        """One-shot subprocess solve of ``formulas`` (optionally via
        ``(check-sat-using tactic)``). Used for the fallback strategies:
        check-sat-using degrades badly under an open push scope (measured 13s
        one-shot vs 90s+ timeout under push -- z3 weakens solve-eqs when it
        must preserve incremental state), and the closed slice needs a fresh
        context anyway. Returns ``(verdict, stdout)`` with verdict True/False/
        None for sat/unsat/anything-else; ``probes`` values (if any) are in
        the stdout. A sat carries no in-process model -- callers treat it as
        inconclusive unless they read the probes."""
        name = f"d{k}_{rung}_{label}.smt2"
        path = (self.dumper.dump_dir if self.dumper is not None else self._scratch) / name
        with self.metrics.timed(f"{label}_serialize"):
            _write_query(
                path,
                formulas,
                f"(check-sat-using {tactic})" if tactic else "(check-sat)",
                comment=f"one-shot {label} query, disjunct {k}, rung {rung}",
                probes=probes,
            )
        budget_s = max(1, budget_ms // 1000)
        t0 = time.perf_counter()
        with self.metrics.timed(f"solve_{rung}_{label}"):
            try:
                proc = subprocess.run(
                    [ARGS().solver, *(z3_args or []), f"-T:{budget_s}", str(path)],
                    capture_output=True,
                    text=True,
                    timeout=budget_s + 30,
                )
                stdout = proc.stdout or ""
                lines = stdout.strip().splitlines()
                ans = lines[0] if lines else ""
            except (subprocess.TimeoutExpired, OSError):
                stdout = ""
                ans = ""
        if self.dumper is not None:
            self.dumper.records.append(
                {
                    "disjunct": k,
                    "file": name,
                    "rung": f"{rung}-{label}-oneshot",
                    "cegar_round": None,
                    "slice_size": slice_size,
                    "result": ans or "unknown",
                    "time_s": round(time.perf_counter() - t0, 4),
                }
            )
        if ans == "unsat":
            return False, stdout
        if ans == "sat":
            return True, stdout
        return None, stdout

    def _try_strategy(self, strategy: str, k: int, rung: str, d: FNode,
                      tactic_indices: frozenset[int],
                      extra: list[FNode] | None) -> bool | None:
        """Run one fallback strategy; returns False (refuted) / True / None."""
        if strategy in ("closed", "closed_int"):
            indices = self._closed_slice(d)
            if not indices:
                return None
            formulas = [self.ctx[i] for i in sorted(indices)] + [d]
            if strategy == "closed":
                return self._closed_abstract(k, rung, formulas, len(indices))
            # interpreted flow: arith.solver=2 (legacy simplex) handles the
            # quotient case-splitting far better than the default (87.6s ->
            # 3.4s); decides what the abstraction leaves inconclusive.
            res, _ = self._oneshot(k, rung, formulas, label="closed_int",
                                   budget_ms=self.budgets.closed_ms,
                                   z3_args=["smt.arith.solver=2"],
                                   slice_size=len(indices))
            return res
        formulas = [self.ctx[i] for i in sorted(tactic_indices)] + list(extra or []) + [d]
        res, _ = self._oneshot(k, rung, formulas, label="tactic",
                               budget_ms=self.budgets.tactic_ms,
                               tactic=self.retry_tactic,
                               slice_size=len(tactic_indices))
        return res

    def _closed_abstract(self, k: int, rung: str, formulas: list[FNode],
                         slice_size: int) -> bool | None:
        """Model-guided mod abstraction (CEGAR over the mod axioms).

        Solve the pure-EUF abstraction; while sat, read the model values of
        each ``umod`` application and its argument (named probes), add the
        quotient-free axiom instances ONLY for the applications the model
        falsifies, and re-solve. Axiom count is proof-driven, not
        slice-size-driven. An axiom-consistent sat proves nothing about real
        mod (only the no-wrap case is axiomatized) -- inconclusive, falls to
        the interpreted strategy."""
        with self.metrics.timed("mod_abstraction"):
            rewritten, apps = _abstract_mods(formulas)
        probes = [(f"appv!{i}", u) for i, u in enumerate(apps)] + [
            (f"argv!{i}", u.arg(0)) for i, u in enumerate(apps)
        ]
        axiomatized: set[FNode] = set()
        axioms: list[FNode] = []
        # Eager instantiation when the instance set is small: the default UF
        # model violates essentially EVERY application at once (measured
        # 2689/2693), so model guidance degenerates to eager plus an extra
        # solver round (0.5s eager vs 1.3s lazy on the worst specimen). The
        # model-guided loop below remains the fallback for slices whose
        # eager set would be too large.
        if len(apps) * 2 <= 8000:
            axiomatized.update(apps)
            for u in apps:
                axioms.extend(_mod_axioms(u))
        for _round in range(self.budgets.cegar_iters + 1):
            self.metrics.count("mod_cegar_rounds")
            res, stdout = self._oneshot(
                k, rung, axioms + rewritten, label="closed",
                budget_ms=self.budgets.closed_ms, slice_size=slice_size,
                probes=probes if apps else None,
            )
            if res is False:
                self.metrics.count("mod_axioms_used", len(axioms))
                return False
            if res is not True or not apps:
                return None
            violated = _violated_apps(apps, stdout)
            if not violated:
                return None  # abstraction-consistent model: inconclusive
            fresh = [u for u in violated if u not in axiomatized]
            if not fresh:
                return None
            axiomatized.update(fresh)
            for u in fresh:
                axioms.extend(_mod_axioms(u))
            self.metrics.count("mod_axioms_added", 2 * len(fresh))
        return None

    def _solve_under(self, s, k: int, d: FNode, *, rung: str,
                     considered: frozenset[int], full_ctx: bool = False,
                     extra: list[FNode] | None = None,
                     prefer: str | None = None,
                     fallback: str | None = None,
                     tactic_indices: frozenset[int] | None = None) -> _Outcome:
        """push; assert [extra +] d; solve; CEGAR on sat (inside the push
        scope); pop.

        ``considered`` = ctx indices asserted in ``s`` including ``extra``
        (a slice-SAT model must be validated against everything else). With
        ``full_ctx`` the solver holds ALL of ctx, so sat is a genuine
        counterexample -- the model is extracted before the pop and no CEGAR
        runs.

        Fallback strategies on unknown, in order: "closed" (tiny closed
        slice, plain z3, ~0.3s) then "tactic" (one-shot retry tactic over
        ``tactic_indices``, default ``considered``). ``prefer`` (locality
        heuristic: hard families cluster, so the strategy that refuted the
        IMMEDIATELY preceding disjunct) runs BEFORE touching the incremental
        solver at all — it must not be sticky: a stale preempt makes every
        easy disjunct pay a one-shot subprocess instead of a ~ms incremental
        solve (measured: stalls a 12k-disjunct batch). ``fallback`` (sticky
        across interleaved easy wins) only reorders the on-unknown strategy
        list, so a hard family member skips wrong strategies after paying
        the primary-rung timeout."""
        tactic_indices = tactic_indices if tactic_indices is not None else considered
        strategies = ["closed", "closed_int"] + (["tactic"] if self.retry_tactic else [])
        if fallback in strategies:
            strategies = [fallback] + [st for st in strategies if st != fallback]
        tried: set[str] = set()

        if prefer in strategies:
            res = self._try_strategy(prefer, k, rung, d, tactic_indices, extra)
            tried.add(prefer)
            self.metrics.count(
                f"{prefer}_first_{'unsat' if res is False else 'sat' if res else 'unknown'}"
            )
            if res is False:
                self.metrics.count("prefer_hit")
                return _Outcome(_Kind.REFUTED, via=prefer)
            self.metrics.count("prefer_miss")

        s.push()
        if extra:
            with self.metrics.timed("assert_replay_escalated"):
                for f in extra:
                    s.add_assertion(f)
        s.add_assertion(d)
        t0 = time.perf_counter()
        try:
            with self.metrics.timed(f"solve_{rung}"):
                sat = s.solve()
        except SolverReturnedUnknownResultError:
            for strategy in strategies:
                if strategy in tried:
                    continue
                res = self._try_strategy(strategy, k, rung, d, tactic_indices, extra)
                self.metrics.count(
                    f"{strategy}_retry_{'unsat' if res is False else 'sat' if res else 'unknown'}"
                )
                if res is False:
                    s.pop()
                    return _Outcome(_Kind.REFUTED, via=strategy)
            reason = _reason_unknown(s)
            self._dump(k, rung, considered, d, "unknown", time.perf_counter() - t0)
            s.pop()
            self.metrics.count(f"unknown_{rung}")
            return _Outcome(_Kind.UNKNOWN, reason=reason)
        if not sat:
            self._dump(k, rung, considered, d, "unsat",
                       time.perf_counter() - t0, interesting=False)
            s.pop()
            return _Outcome(_Kind.REFUTED)
        self._dump(k, rung, considered, d, "sat", time.perf_counter() - t0)
        if full_ctx:
            with self.metrics.timed("model_extract"):
                model = _extract_model(s)
            s.pop()
            return _Outcome(_Kind.SAT_VALIDATED, model=model)
        outcome = self._run_cegar(s, k, d, considered, rung)
        s.pop()
        return outcome

    def _run_cegar(self, s, k: int, d: FNode, considered: frozenset[int], rung: str) -> _Outcome:
        """Validate the slice model against omitted ctx constraints; assert the
        falsified ones and re-solve (still inside the push scope, so the pop
        cleans up). Runs while z3 keeps finding slice models."""
        self.metrics.count("cegar_invocations")
        considered = set(considered)
        for it in range(self.budgets.cegar_iters):
            self.metrics.count("cegar_rounds")
            with self.metrics.timed("model_extract"):
                model = _extract_model(s)
            subs = {
                sym: val
                for sym, val in model
                if val.is_int_constant() or val.is_bool_constant()
            }
            with self.metrics.timed("model_eval"):
                falsified, n_undetermined = self._classify_omitted(subs, considered)
            if falsified:
                self.metrics.count("cegar_constraints_added", len(falsified))
                for i in falsified:
                    s.add_assertion(self.ctx[i])
                considered.update(falsified)
                t0 = time.perf_counter()
                try:
                    with self.metrics.timed(f"solve_{rung}_cegar"):
                        sat = s.solve()
                except SolverReturnedUnknownResultError:
                    self._dump(k, rung, considered, d, "unknown",
                               time.perf_counter() - t0, cegar_round=it)
                    self.metrics.count(f"unknown_{rung}_cegar")
                    return _Outcome(_Kind.UNKNOWN, reason=_reason_unknown(s))
                dt = time.perf_counter() - t0
                if not sat:
                    self._dump(k, rung, considered, d, "unsat", dt, cegar_round=it)
                    return _Outcome(_Kind.REFUTED, via_cegar=True)
                self._dump(k, rung, considered, d, "sat", dt, cegar_round=it)
                continue
            if n_undetermined == 0:
                # every omitted constraint evaluated to true under the model:
                # the model satisfies ALL of ctx -- a genuine counterexample.
                self.metrics.count("cegar_validated_sat")
                if self.debug:
                    self._debug_recheck_model(subs)
                return _Outcome(_Kind.SAT_VALIDATED, model=model)
            self.metrics.count("cegar_undetermined_escalations")
            return _Outcome(_Kind.SAT_CANDIDATE)
        self.metrics.count("cegar_iters_exhausted")
        return _Outcome(_Kind.SAT_CANDIDATE)

    def _classify_omitted(self, subs: dict, considered: set[int]) -> tuple[list[int], int]:
        """Partially evaluate each omitted ctx constraint under the model.

        Returns ``(falsified, n_undetermined)``. Constraints whose free vars
        are disjoint from the model are undetermined without substitution
        (the common case by COI construction). ``n_undetermined`` only
        matters when nothing is falsified, and falsified is capped at
        ``cegar_batch``."""
        model_vars = frozenset(subs)
        falsified: list[int] = []
        n_undetermined = 0
        free_vars = self.index.free_vars
        for i in range(len(self.ctx)):
            if i in considered:
                continue
            fvs = free_vars[i]
            if fvs.isdisjoint(model_vars):
                n_undetermined += 1
                continue
            self.metrics.count("model_eval_substitutions")
            val = substitute_no_validate(self.ctx[i], subs).simplify()
            if val.is_false():
                falsified.append(i)
                if len(falsified) >= self.budgets.cegar_batch:
                    break
            elif not val.is_true():
                n_undetermined += 1
        return falsified, n_undetermined

    def _debug_recheck_model(self, subs: dict):
        """Belt-and-braces (--sliced-debug): a CEGAR-validated sat model must
        satisfy every ctx conjunct."""
        for i, c in enumerate(self.ctx):
            val = substitute_no_validate(c, subs).simplify()
            assert val.is_true(), f"validated-sat model does not satisfy ctx[{i}]: {c}"

    def _dump(self, k, rung, considered, d, result, time_s, cegar_round=None, interesting=True):
        if self.dumper is None:
            return
        formulas = [self.ctx[i] for i in sorted(considered)] + [d]
        self.dumper.dump(
            k=k, rung=rung, formulas=formulas, result=result, time_s=time_s,
            slice_size=len(considered), cegar_round=cegar_round, interesting=interesting,
        )

    # ---------------- the run loop ----------------

    def run(self, attempt: Action) -> str:
        disjuncts = self.disjuncts

        # Phase 1: syntactic discharge + slice-key classification (no solver).
        groups: dict[frozenset, list[int]] = {}
        for k, d in enumerate(disjuncts):
            with self.metrics.timed("syntactic_simplify"):
                syntactically_false = d.simplify().is_false()
            if syntactically_false:
                self.tiers["syntactic"] += 1
                self.refuted.add(d)
                continue
            key = self.index.slice_seed(d)
            groups.setdefault(key, []).append(k)
        self.metrics.count("n_slice_groups", len(groups))

        n_refuted = self.tiers["syntactic"]
        result: str | None = None
        n_processed = 0
        t_start = time.perf_counter()

        # Phase 2: compute slices and batch by slice, ASCENDING size. All
        # non-empty slices share the growing solver (delta asserts + GC);
        # the ascending order makes the resident context grow monotonically,
        # so near-identical big slices are asserted once, not per group.
        # Empty slices (memory-only disjuncts) share the memory-argument
        # solver, processed last.
        slice_batches: list[tuple[frozenset, list[int]]] = []
        mem_members: list[int] = []
        for key, members in groups.items():
            slice_idx = self._slice_for(key) if key else frozenset()
            if not slice_idx:
                mem_members.extend(members)
            else:
                slice_batches.append((slice_idx, members))
        slice_batches.sort(key=lambda b: len(b[0]))
        self.metrics.count("n_slice_batches", len(slice_batches))
        self.metrics.count("n_mem_disjuncts", len(mem_members))

        batches: list[tuple[str, frozenset, list[int]]] = list(
            ("arith", sl, m) for sl, m in slice_batches
        )
        if mem_members:
            batches.append(("mem", self.index.mem_indices, mem_members))

        for primary_rung, slice_idx, members in batches:
            if primary_rung == "arith":
                group_solver, primary_considered = self.grow_solver_for(slice_idx)
            else:
                group_solver = self.mem_solver()
                primary_considered = slice_idx

            prefer: str | None = None  # preempt: strategy that won the previous disjunct
            sticky: str | None = None  # fallback ordering: last non-default winner in batch
            for k in members:
                n_processed += 1
                if n_processed % 1000 == 0:
                    logging.warning(
                        "sliced check: %d/%d disjuncts, %d refuted, tiers=%s, %.1fs",
                        n_processed,
                        len(disjuncts),
                        n_refuted,
                        dict(self.tiers),
                        time.perf_counter() - t_start,
                    )
                d = disjuncts[k]
                if d in self.refuted:
                    self.tiers["cached"] += 1
                    n_refuted += 1
                    continue
                t_disjunct = time.perf_counter()
                # Class routing: structure-keyed preference (learned from
                # earlier wins) fills in when there is no fresher neighbor
                # preempt — hard families are structural, not positional, so
                # interleaved members no longer pay the primary-rung toll.
                ckey = _structure_key(d) if self.router is not None else None
                class_prefer = self.router.route(ckey) if self.router else None
                effective_prefer = prefer or class_prefer
                tier, outcome = self._ladder(
                    group_solver, k, d, primary_rung, primary_considered, slice_idx,
                    prefer=effective_prefer, fallback=sticky,
                )
                if self.router is not None:
                    self.router.learn(
                        ckey,
                        outcome.via,
                        routed=prefer is None and class_prefer is not None,
                        hit=outcome.via is not None
                        and outcome.via == class_prefer,
                    )
                # Preempt (prefer) is NOT sticky: hard families cluster, so
                # only the immediate neighbor gets the run-strategy-first
                # shortcut; a stale preempt makes every easy disjunct pay a
                # one-shot subprocess (measured: stalls a 12k batch). The
                # sticky memory survives interleaved easy wins but only
                # reorders the on-unknown fallback list. prefer_hit/miss
                # count how the preempt guess performs.
                prefer = outcome.via
                sticky = outcome.via or sticky
                if self.debug:
                    self.disjunct_rows.append(
                        {
                            "index": k,
                            "tier": tier,
                            "kind": outcome.kind.value,
                            "slice_size": len(primary_considered),
                            "time_s": round(time.perf_counter() - t_disjunct, 4),
                        }
                    )
                assert outcome.kind is not _Kind.SAT_CANDIDATE, (
                    "slice-level sat must never surface as a verdict"
                )
                if outcome.kind is _Kind.REFUTED:
                    self.tiers[tier] += 1
                    n_refuted += 1
                    self.refuted.add(d)
                    with self.metrics.timed("learn_not_d"):
                        group_solver.add_assertion(Not(d))
                    continue
                if outcome.kind is _Kind.SAT_VALIDATED:
                    attempt += {
                        "result": "sat",
                        "model": to_nice_model(outcome.model),
                        "disjunct_index": k,
                    }
                    result = "sat"
                    break
                # UNKNOWN after the full ladder.
                reason = outcome.reason
                record = {"index": k, "reason": reason or ""}
                if self.collect_unknowns is None:
                    attempt += {
                        "result": f"unknown-{reason}" if reason else "unknown",
                        "disjunct_index": k,
                    }
                    result = attempt.result
                    break
                if self.collect_unknowns < 0 or len(self.unknown_disjuncts) < self.collect_unknowns:
                    self.unknown_disjuncts.append(record)
                logging.warning("disjunct %d unknown (%s); continuing", k, reason)
            # the growing/mem solvers persist across batches; close() cleans up
            if result is not None:
                break

        if result is None:
            if self.unknown_disjuncts:
                attempt += {"result": "unknown"}
            else:
                # Soundness: unsat only when every disjunct was refuted.
                assert n_refuted == len(disjuncts), (n_refuted, len(disjuncts))
                attempt += {"result": "unsat"}
        return attempt.result

    def _ladder(self, group_solver, k: int, d: FNode, primary_rung: str,
                primary_considered: frozenset[int],
                slice_idx: frozenset[int], *,
                prefer: str | None = None,
                fallback: str | None = None) -> tuple[str, _Outcome]:
        """Primary rung (arith/mem), then escalation, then full context.

        ``primary_considered`` is what the primary solver actually holds
        (resident set, may exceed the exact ``slice_idx`` by pollution)."""
        outcome = self._solve_under(
            group_solver, k, d, rung=primary_rung, considered=primary_considered,
            prefer=prefer, fallback=fallback,
            # the one-shot uses the EXACT slice, not the (polluted) resident
            # set -- the standalone-win measurements were on exact slices
            tactic_indices=slice_idx,
        )
        if outcome.kind in (_Kind.REFUTED, _Kind.SAT_VALIDATED):
            tier = (
                primary_rung
                + ("+cegar" if outcome.via_cegar else "")
                + (f"+{outcome.via}" if outcome.via else "")
            )
            return tier, outcome

        if len(self.hard_disjuncts) < _HARD_DISJUNCTS_CAP:
            self.hard_disjuncts.append(k)

        if primary_rung == "arith" and len(slice_idx) <= self.budgets.small_slice:
            # Escalate to slice ∪ memory-argument WITHOUT a fresh replay:
            # push the (small) slice into a scope of the shared mem solver.
            # Big slices skip this -- pushing ~13k constraints per escalation
            # would dominate; they go straight to the full-context solver.
            self.metrics.count("escalations_to_mem_union")
            extra = [self.ctx[i] for i in sorted(slice_idx)]
            considered = slice_idx | self.index.mem_indices
            outcome = self._solve_under(
                self.mem_solver(), k, d, rung="escalated",
                considered=considered, extra=extra,
            )
            if outcome.kind in (_Kind.REFUTED, _Kind.SAT_VALIDATED):
                return "escalated", outcome

        self.metrics.count("escalations_to_full")
        outcome = self._solve_under(
            self.full_solver(), k, d, rung="full",
            considered=self._all_indices, full_ctx=True,
        )
        return "full", outcome

    def report(self, attempt: Action):
        attempt += {
            "mode": "sliced",
            "n_disjuncts": len(self.disjuncts),
            "n_ctx": len(self.ctx),
            "n_boundary_vars": len(self.index.boundary),
            "n_mem_constraints": len(self.index.mem_indices),
            "tiers": dict(self.tiers),
            "hard_disjuncts": self.hard_disjuncts,
            "metrics": self.metrics.as_dict(),
        }
        if self.unknown_disjuncts:
            attempt += {"unknown_disjuncts": self.unknown_disjuncts}
        if self.debug:
            attempt += {"disjuncts": self.disjunct_rows}


def _reason_unknown(solver) -> str | None:
    from ..checker import _get_reason_unknown

    return _get_reason_unknown(solver)


def check_smt_script_sliced(
    goal: FNode,
    ctx: list[FNode],
    action: Action,
    *,
    input_for_log: Path | None = None,
    budgets: SliceBudgets | None = None,
    boundary_pattern: re.Pattern | None = None,
    collect_unknowns: int | None = None,
    debug: bool = False,
    dump_dir: Path | None = None,
    dump_all: bool = False,
    retry_tactic: str | None = None,
) -> str:
    """Prove ``ctx ∧ goal`` unsat disjunct-by-disjunct via boundary-stopped
    COI slices (see module docstring). Wired to ``main.py check --solve-sliced``."""
    from ..checker import _display_path, _finalize_result

    budgets = budgets if budgets is not None else SliceBudgets.from_args()
    if boundary_pattern is None:
        boundary_pattern = re.compile(
            getattr(ARGS(), "boundary_regex", None) or DEFAULT_BOUNDARY_REGEX
        )
    metrics = Metrics()
    dumper = _SliceDumper(dump_dir, dump_all) if dump_dir is not None else None
    logging.warning(
        "check %s (sliced): %d ctx conjuncts, %d disjuncts, boundary=%s",
        _display_path(input_for_log),
        len(ctx),
        len(goal.args()),
        boundary_pattern.pattern,
    )
    with Action("check-attempt") as attempt:
        attempt += {
            "solver": ARGS().solver,
            "solver_options": {
                "timeout": budgets.full_ms,
                "smt.random_seed": 0,
                "sat.random_seed": 0,
            },
        }
        if retry_tactic is None:
            retry_tactic = getattr(ARGS(), "sliced_tactic", None)
            if retry_tactic is None:
                retry_tactic = DEFAULT_RETRY_TACTIC
        checker = _SlicedChecker(
            ctx,
            goal,
            budgets=budgets,
            boundary_pattern=boundary_pattern,
            metrics=metrics,
            dumper=dumper,
            collect_unknowns=collect_unknowns,
            debug=debug,
            retry_tactic=retry_tactic,
        )
        try:
            checker.run(attempt)
        except BrokenPipeError:
            attempt += {"result": "error-broken-pipe"}
        finally:
            checker.report(attempt)
            checker.close()
    for line in metrics.summary_lines():
        logging.info(line)
    return _finalize_result(action, attempt)
