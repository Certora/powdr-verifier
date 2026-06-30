"""Render membus stats / info as rich, plain text, or JSON.

Reuses lens's output conventions: `Target`, `default_mode`, and the
RICH/PLAIN/JSON mode constants. `extract` output is the busat `.bus` text itself
(emitted by `extract.build`), so it has no renderer here.
"""
from __future__ import annotations

import json

from src.lens.render import JSON, PLAIN, RICH, Target, default_mode  # noqa: F401 (re-exported)

from .meminfo import InfoRow
from .memstats import MemStats
from .solve import Solution

_KIND_COLOR = {"send": "green", "recv": "red", "sym": "yellow"}
_AS_PALETTE = ["cyan", "magenta", "blue", "bright_green", "bright_red"]


def _kind_markup(kind: str) -> str:
    c = _KIND_COLOR.get(kind)
    return f"[{c}]{kind}[/]" if c else kind


def _as_markup(asv: str) -> str:
    if asv == "sym":
        return "[yellow]sym[/]"
    try:
        c = _AS_PALETTE[int(asv) % len(_AS_PALETTE)]
        return f"[{c}]{asv}[/]"
    except ValueError:
        return asv


_IO_COLOR = {"in": "cyan", "out": "magenta"}


def _io_markup(io: str) -> str:
    c = _IO_COLOR.get(io)
    return f"[{c}]{io}[/]" if c else io


# --------------------------------------------------------------------------- #
# stats
# --------------------------------------------------------------------------- #
def render_stats(stats: MemStats, target: Target, mode: str) -> str:
    if mode == JSON:
        return json.dumps({"target": vars(target), **stats.as_dict()}, indent=2)
    if mode == RICH:
        return _stats_rich(stats, target)
    return _stats_plain(stats, target)


def _precond(stats: MemStats) -> str:
    return (f"sends_ordered={'yes' if stats.sends_ordered else 'NO'} "
            f"recvs_bounded={'yes' if stats.recvs_bounded else 'NO'} "
            f"duplicates={stats.duplicates}")


def _stats_plain(s: MemStats, t: Target) -> str:
    out = [f"# {t.group}/{t.block} {t.label}  ({t.path})",
           f"memory_bus_id\t{s.mem_id}",
           f"n_memory\t{s.n_memory}",
           f"preconditions\t{_precond(s)}",
           "as\tcount\tsend\trecv\tbal\tsymKey\tdistinct\talias\treason"]
    for a in s.address_spaces:
        out.append(f"{a.addr_space}\t{a.count}\t{a.send}\t{a.recv}\t"
                   f"{'ok' if a.balanced else 'NO'}\t{a.sym_key}\t{a.distinct_keys}\t"
                   f"{'det' if a.determined else 'UNDET'}\t{a.reason}")
    return "\n".join(out)


def _stats_rich(s: MemStats, t: Target) -> str:
    from rich.console import Console
    from rich.table import Table

    table = Table(title=f"{t.group}/{t.block} {t.label} — memory bus (id {s.mem_id})")
    for col in ("as", "count", "send", "recv", "bal", "symKey", "distinct", "alias", "reason"):
        table.add_column(col)
    for a in s.address_spaces:
        table.add_row(_as_markup(a.addr_space), str(a.count),
                      f"[green]{a.send}[/]", f"[red]{a.recv}[/]",
                      "[green]ok[/]" if a.balanced else "[red]NO[/]",
                      str(a.sym_key), str(a.distinct_keys),
                      "det" if a.determined else "[yellow]UNDET[/]", a.reason)
    con = Console()
    with con.capture() as cap:
        con.print(table)
        con.print(f"n_memory={s.n_memory}  preconditions: {_precond(s)}")
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# info
# --------------------------------------------------------------------------- #
def render_info(rows: list[InfoRow], target: Target, mode: str, total: int | None = None) -> str:
    if total is None:
        total = len(rows)
    if mode == JSON:
        return json.dumps({"target": vars(target), "total": total, "shown": len(rows),
                           "interactions": [r.as_dict() for r in rows]}, indent=2)
    if mode == RICH:
        return _info_rich(rows, target, total)
    return _info_plain(rows, target, total)


def _count_note(shown: int, total: int) -> str:
    if shown < total:
        return f"{total} memory interactions (showing {shown}; --limit 0 for all)"
    return f"{total} memory interactions"


def _info_plain(rows: list[InfoRow], t: Target, total: int) -> str:
    out = [f"# {t.group}/{t.block} {t.label}  ({t.path})",
           f"# {_count_note(len(rows), total)}",
           "ord\tkind\tas\tclass\tkey\ttime\tacc\tts_col"]
    for r in rows:
        out.append(f"{r.ordinal}\t{r.kind}\t{r.addr_space}\t{r.alias_class}\t{r.key}\t"
                   f"{r.time}\t{'' if r.access is None else r.access}\t{r.ts_col}")
    return "\n".join(out)


def _info_rich(rows: list[InfoRow], t: Target, total: int) -> str:
    from rich.console import Console
    from rich.table import Table

    table = Table(title=f"{t.group}/{t.block} {t.label} — {_count_note(len(rows), total)}")
    for col in ("ord", "kind", "as", "class", "key", "time", "acc"):
        table.add_column(col)
    for r in rows:
        table.add_row(str(r.ordinal), _kind_markup(r.kind), _as_markup(r.addr_space),
                      str(r.alias_class), r.key,
                      ("[green]" if r.kind == "send" else "[red]") + r.time + "[/]"
                      if r.kind in ("send", "recv") else r.time,
                      "" if r.access is None else str(r.access))
    con = Console()
    with con.capture() as cap:
        con.print(table)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# solve
# --------------------------------------------------------------------------- #
def render_solve(sol: "Solution", target: Target, mode: str) -> str:
    if mode == JSON:
        return json.dumps({"target": vars(target), **sol.as_dict()}, indent=2)
    if mode == RICH:
        return _solve_rich(sol, target)
    return _solve_plain(sol, target)


def _solve_summary(s: "Solution") -> str:
    exit_s = "?" if s.ts_exit is None else f"T+{s.ts_exit}"
    uniq = "yes" if s.unique else "no/unknown"
    notes = [f"{c.key}:{c.note}" for c in s.cells if c.note]
    tail = f"  unsolved_cells={','.join(notes)}" if notes else ""
    iv = "  [assumed is_valid=1]" if s.assumed_is_valid else ""
    return (f"as={s.addr_space} cells={len(s.cells)} inputs={s.n_inputs} "
            f"outputs={s.n_outputs} ts_entry=T+0 ts_exit={exit_s} unique={uniq}{iv}{tail}")


def _solve_plain(s: "Solution", t: Target) -> str:
    out = [f"# {t.group}/{t.block} {t.label}  ({t.path})",
           f"# {_solve_summary(s)}",
           "id\tio\tkind\tkey\tvtime\tflow"]
    for r in s.rows:
        out.append(f"{r.ordinal}\t{r.io}\t{r.kind}\t{r.key}\t{r.vtime}\t{r.flow}")
    return "\n".join(out)


def _solve_rich(s: "Solution", t: Target) -> str:
    from rich.console import Console
    from rich.table import Table

    table = Table(title=f"{t.group}/{t.block} {t.label} — solve {_solve_summary(s)}")
    for col in ("id", "io", "kind", "key", "vtime", "flow"):
        table.add_column(col)
    for r in s.rows:
        table.add_row(str(r.ordinal), _io_markup(r.io), _kind_markup(r.kind), r.key,
                      ("[green]" if r.kind == "send" else "[red]") + r.vtime + "[/]",
                      r.flow)
    con = Console()
    with con.capture() as cap:
        con.print(table)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# agent guide
# --------------------------------------------------------------------------- #
def agent_guide() -> str:
    return AGENT_GUIDE.strip()


AGENT_GUIDE = """
membus — examine / extract / align the MEMORY bus (id 1) of powdr APC dumps.

WHAT / WHY
  A memory interaction is a send (mult 1) or recv (mult -1) on bus 1, with
  args = [address_space, pointer, b0, b1, b2, b3, timestamp]. The pass we study
  (`memory`) removes interactions; removal is sound iff, per alias class, the
  send<->recv pairing is forced. membus surfaces the pieces that decide that:
  the recovered KEY (address), the timestamp ORDER, and the alias structure.

DECIDE (goal -> command)
  shape of one circuit's memory bus      -> stats  <group> <block> <step>
  per-interaction key/timestamp/alias    -> info   <group> <block> <step> [--as N]
  solve matching: inputs/outputs/flow    -> solve  <group> <block> <step> [--as N]
  emit busat .bus (abstract ts order)    -> extract <group> <block> <stepA> [stepB]
  (align two circuits' memory busses     -> align   ... [v2, not yet implemented])

INPUT
  Auto-discovered the lens way: <group> <block> <step> (e.g. keccak 2100224 022),
  resolved via the same mechanism as `lens`. Or explicit files: --file-a PATH
  (and --file-b PATH for the second circuit). Two-circuit forms take a second
  pass of the SAME block as <stepB> (or --file-b).

KEYS & ALIASING
  recover_key -> const <v> (fixed address) | <base>+<off> (symbolic, recovered
  from the limb gadget) | unresolved(...). An address space partitions into
  provably-disjoint alias sets only when keys are all-constant, or all base+off
  sharing ONE base. Otherwise (multiple bases / unresolved) aliasing is NOT
  statically decidable and is flagged UNDET — do not assume disjointness.

PRECONDITIONS (shown by `stats`)
  sends_ordered: every send timestamp lies in the deduced total order (R1 chain).
  recvs_bounded: every recv timestamp is bounded below its own send (R2).
  Both must hold for `extract` to emit a well-formed abstract-order .bus.

EXTRACT OUTPUT
  busat .bus: MEM rows (abstract ts symbols), DEFS (base+offset keys), and
  CONSTRAINTS = strict `<` order edges, each preceded by a `# justification`.
  One circuit -> all memory interactions; two -> only the REMOVED set (A - B).

SOLVE (v1: AS1, constant keys, graph solver; fails gracefully otherwise)
  Solves the bus constraints (no memory-consistency assumption) to recover, per
  cell, the recv<->send matching, and marks each interaction in/out/flow:
    input  = the recv reading the entry value (prev_ts < ts_entry);
    output = the lone send no recv reads (escapes the block);
    flow   = recv "← #send" reads that send; send "→ #recv" is read by it.
  vtime is virtual time relative to ts_entry (T+0); ts_exit = last clock. Any
  complete mapping is a solution; `unique` reports whether it is forced. Row id
  is the membus ordinal, stable across --as so solutions can be merged.

LIMITATIONS (v1)
  Symbolic base+offset recovery is calibrated to the keccak (2100224) dumps
  (ADDR_SCALE=30720); other shapes report `unresolved` (never wrong). Constant
  keys are fully general. Aliasing across distinct symbolic bases is reported,
  not asserted.
"""
