"""Render DumpStats / DumpDiff as rich, plain text, or JSON."""
import json
import sys
from dataclasses import dataclass

from .metrics import DumpDiff, DumpStats

RICH, PLAIN, JSON = "rich", "plain", "json"


@dataclass
class Target:
    """What was resolved, for headers."""

    group: str
    block: str
    label: str  # e.g. "011_memory"
    path: str


def default_mode() -> str:
    """rich on a TTY, plain otherwise (pipes, agents, CI)."""
    return RICH if sys.stdout.isatty() else PLAIN


def _delta_str(d: int) -> str:
    return "" if d == 0 else f"{d:+d}"


# --------------------------------------------------------------------------- #
# show
# --------------------------------------------------------------------------- #
def render_show(stats: DumpStats, target: Target, mode: str) -> str:
    if mode == JSON:
        return json.dumps({"target": vars(target), **stats.as_dict()}, indent=2)
    if mode == RICH:
        return _show_rich(stats, target)
    return _show_plain(stats, target)


def _show_plain(s: DumpStats, t: Target) -> str:
    out: list[str] = []
    out.append(f"# {t.group}/{t.block} {t.label}  ({t.path})")
    out.append(f"format\t{s.fmt}")
    out.append(f"constraints\t{s.n_constraints}")
    out.append(f"bus_interactions\t{s.n_bus_interactions}")
    out.append(f"derived_columns\t{s.n_derived_columns}")
    out.append(f"distinct_columns\t{s.distinct_columns}")
    out.append(
        f"degree\tmin={s.degree.min} mean={s.degree.mean} max={s.degree.max}"
    )
    out.append(f"nodes\tmin={s.nodes.min} mean={s.nodes.mean} max={s.nodes.max}")
    out.append(f"depth\tmin={s.depth.min} mean={s.depth.mean} max={s.depth.max}")
    out.append("ops\t" + " ".join(f"{k}={v}" for k, v in sorted(s.op_hist.items())))
    if s.degree_hist:
        out.append(
            "degree_hist\t"
            + " ".join(f"{k}:{v}" for k, v in sorted(s.degree_hist.items()))
        )
    if s.derived_forms:
        out.append(
            "derived_forms\t"
            + " ".join(f"{k}={v}" for k, v in sorted(s.derived_forms.items()))
        )
    if s.n_blocks is not None:
        out.append(f"blocks\t{s.n_blocks}")
        out.append(f"instructions\t{s.n_instructions}")
    if s.submachine_polys is not None:
        out.append(
            f"submachines\t{len(s.submachine_polys)} "
            f"polys={s.submachine_polys}"
        )
    out.append("# buses\tid\tlabel\tcount\tsend\trecv\tsym\tother\targs_nodes")
    for r in s.buses:
        out.append(
            f"bus\t{r.id}\t{r.label}\t{r.count}\t{r.send}\t{r.recv}\t"
            f"{r.sym}\t{r.other}\t{r.args_nodes}"
        )
    return "\n".join(out)


def _show_rich(s: DumpStats, t: Target) -> str:
    from rich.console import Console
    from rich.table import Table

    console = Console()
    with console.capture() as cap:
        console.rule(f"[bold]{t.group}/{t.block}[/]  {t.label}  "
                     f"[magenta]({s.fmt})[/]")

        counts = Table.grid(padding=(0, 2))
        counts.add_column(style="cyan", justify="right")
        counts.add_column()
        counts.add_row("format", f"[magenta]{s.fmt}[/]")
        counts.add_row("constraints", str(s.n_constraints))
        counts.add_row("bus_interactions", str(s.n_bus_interactions))
        counts.add_row("derived_columns", str(s.n_derived_columns))
        counts.add_row("distinct_columns", str(s.distinct_columns))
        counts.add_row(
            "degree (min/mean/max)",
            f"{s.degree.min} / {s.degree.mean} / [bold]{s.degree.max}[/]",
        )
        counts.add_row("nodes (min/mean/max)", f"{s.nodes.min} / {s.nodes.mean} / {s.nodes.max}")
        counts.add_row("depth (min/mean/max)", f"{s.depth.min} / {s.depth.mean} / {s.depth.max}")
        counts.add_row("operators", "  ".join(f"{k}={v}" for k, v in sorted(s.op_hist.items())))
        if s.derived_forms:
            counts.add_row(
                "derived_forms",
                "  ".join(f"{k}={v}" for k, v in sorted(s.derived_forms.items())),
            )
        if s.n_blocks is not None:
            counts.add_row("blocks / instructions", f"{s.n_blocks} / {s.n_instructions}")
        if s.submachine_polys is not None:
            counts.add_row(
                "submachines (polys)",
                f"{len(s.submachine_polys)}  {s.submachine_polys}",
            )
        console.print(counts)

        bus = Table(title="bus interactions", title_style="bold", show_edge=False)
        bus.add_column("id", justify="right")
        bus.add_column("label", style="green")
        bus.add_column("count", justify="right")
        bus.add_column("send", justify="right")
        bus.add_column("recv", justify="right")
        bus.add_column("sym", justify="right")
        bus.add_column("other", justify="right")
        bus.add_column("args_nodes", justify="right")
        for r in s.buses:
            bus.add_row(
                r.id, r.label, str(r.count), str(r.send), str(r.recv),
                str(r.sym), str(r.other), str(r.args_nodes),
            )
        console.print(bus)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# compare
# --------------------------------------------------------------------------- #
def render_compare(
    diff: DumpDiff, ta: Target, tb: Target, mode: str
) -> str:
    if mode == JSON:
        return json.dumps(
            {"a": vars(ta), "b": vars(tb), **diff.as_dict()}, indent=2
        )
    if mode == RICH:
        return _compare_rich(diff, ta, tb)
    return _compare_plain(diff, ta, tb)


def _compare_plain(diff: DumpDiff, ta: Target, tb: Target) -> str:
    out: list[str] = []
    out.append(f"# A: {ta.group}/{ta.block} {ta.label} [{diff.a.fmt}]")
    out.append(f"# B: {tb.group}/{tb.block} {tb.label} [{diff.b.fmt}]")
    if diff.a.fmt != diff.b.fmt:
        out.append("# note: formats differ; operator deltas may be encoding artifacts")
    out.append("# metric\tA\tB\tdelta")
    for k, (va, vb) in diff.scalar_deltas().items():
        out.append(f"{k}\t{va}\t{vb}\t{_delta_str(vb - va)}")
    dm = diff.as_dict()["degree_mean"]
    out.append(f"degree_mean\t{dm['a']}\t{dm['b']}\t{dm['delta']:+g}" if dm["delta"] else
               f"degree_mean\t{dm['a']}\t{dm['b']}\t")
    for k, (va, vb) in diff.op_deltas().items():
        out.append(f"op[{k}]\t{va}\t{vb}\t{_delta_str(vb - va)}")
    out.append("# bus\tid\tlabel\tA\tB\tdelta")
    for i, lbl, ca, cb in diff.bus_deltas():
        out.append(f"bus\t{i}\t{lbl}\t{ca}\t{cb}\t{_delta_str(cb - ca)}")
    return "\n".join(out)


def _compare_rich(diff: DumpDiff, ta: Target, tb: Target) -> str:
    from rich.console import Console
    from rich.table import Table

    console = Console()

    def cell(d: int) -> str:
        if d == 0:
            return "[dim]·[/]"
        color = "green" if d < 0 else "red"
        return f"[{color}]{d:+d}[/]"

    with console.capture() as cap:
        console.rule(f"[bold]A[/] {ta.group}/{ta.block} {ta.label} "
                     f"[magenta]({diff.a.fmt})[/]   "
                     f"[bold]B[/] {tb.group}/{tb.block} {tb.label} "
                     f"[magenta]({diff.b.fmt})[/]")
        if diff.a.fmt != diff.b.fmt:
            console.print("[yellow]note:[/] formats differ; "
                          "operator deltas may be encoding artifacts")
        tbl = Table(show_edge=False)
        tbl.add_column("metric", style="cyan")
        tbl.add_column("A", justify="right")
        tbl.add_column("B", justify="right")
        tbl.add_column("Δ", justify="right")
        for k, (va, vb) in diff.scalar_deltas().items():
            tbl.add_row(k, str(va), str(vb), cell(vb - va))
        dm = diff.as_dict()["degree_mean"]
        tbl.add_row("degree_mean", str(dm["a"]), str(dm["b"]),
                    "[dim]·[/]" if dm["delta"] == 0 else f"{dm['delta']:+g}")
        for k, (va, vb) in diff.op_deltas().items():
            tbl.add_row(f"op[{k}]", str(va), str(vb), cell(vb - va))
        console.print(tbl)

        bus = Table(title="bus interactions", title_style="bold", show_edge=False)
        bus.add_column("id", justify="right")
        bus.add_column("label", style="green")
        bus.add_column("A", justify="right")
        bus.add_column("B", justify="right")
        bus.add_column("Δ", justify="right")
        for i, lbl, ca, cb in diff.bus_deltas():
            bus.add_row(i, lbl, str(ca), str(cb), cell(cb - ca))
        console.print(bus)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# agent guide
# --------------------------------------------------------------------------- #
def agent_guide() -> str:
    """Dense, parse-friendly usage doc for agents (the --agent output)."""
    return AGENT_GUIDE.strip()


AGENT_GUIDE = """
lens — statistics over powdr APC JSON dumps.

SUBCOMMANDS
  show    <group> <block> <step>        stats for one dump
  compare <group> <block> <stepA> <stepB>   A->B deltas (same block)

GLOBAL FLAGS
  --root DIR     dumps root (default: powdr-dumps)
  --plain        plain TSV-ish text, no color (default when not a TTY)
  --json         machine-readable JSON (schema below)
  --agent        print this guide and exit
  (no flag on a TTY -> colored rich output)

RESOLUTION
  group   keccak -> <root>/guest-keccak ; also accepts guest-keccak or a path
  block   candidate id, e.g. 2103924 (apc_candidate_ prefix optional)
  step    NNN integer (11 or 011) | pass name (memory) | unopt|base (000)
          pass names repeat (memory at 011/022/033): disambiguate with
          memory@2 (1-based) or use the NNN. Ambiguous bare names error.

FORMAT (powdr emits two dump types; lens auto-detects)
  circuit      Apc/SymbolicMachine (AlgebraicExpression): base _000_unopt
               dump. Has block/subs; uses real - and unary ["-",e].
  constraints  ConstraintSystem (GroupedExpression): per-pass dumps. Only
               +/*; subtraction lowered to + (p-1)*x. Discriminator: no
               block/subs key.
  comparing across formats flags operator-delta artifacts.

JSON FIELDS (show)
  target{group,block,label,path}  format:"circuit"|"constraints"
  n_constraints:int  n_bus_interactions:int  n_derived_columns:int
  distinct_columns:int
  degree{min,mean,max}  degree_hist{deg:count}
  nodes{min,mean,max}  depth{min,mean,max}  op_hist{"+":n,"-":n,"*":n}
  buses[ {id,label,count,send,recv,sym,other,args_nodes} ]
  derived_forms{form:count}
  n_blocks,n_instructions,submachine_polys[]   (base/unopt dump only)
  degree = polynomial degree (const 0, col 1, +/- max, * sum)

JSON FIELDS (compare)
  a{...} b{...} (targets)  format{a,b}
  scalars{metric:{a,b,delta}}  buses[{id,label,a,b,delta}]
  op_hist{op:{a,b,delta}}  degree_mean{a,b,delta}

EXAMPLES
  lens show keccak 2106412 011 --json
  lens show keccak 2106412 memory --plain
  lens compare keccak 2103924 010 011
  lens compare keccak 2103924 memory remove_free --json
"""
