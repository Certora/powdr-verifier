"""Render DumpStats / DumpDiff as rich, plain text, or JSON."""
import json
import sys
from dataclasses import dataclass

from .metrics import DumpDiff, DumpStats

RICH, PLAIN, JSON = "rich", "plain", "json"
FMT_MARK = {"machine": "M", "constraints": "C",
            "substitutions": "S", "unknown": "?"}
_FMT_LEGEND = "f: M=machine C=constraints"


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
# sweep
# --------------------------------------------------------------------------- #
def render_sweep(rows, group: str, block: str, mode: str) -> str:
    from .sweep import abbrev_label

    if mode == JSON:
        return json.dumps(
            {"group": group, "block": block,
             "steps": [r.as_dict() for r in rows]},
            indent=2,
        )
    if mode == RICH:
        return _sweep_rich(rows, group, block, abbrev_label)
    return _sweep_plain(rows, group, block, abbrev_label)


def _sym_cell(row, abbrev) -> str:
    return ",".join(abbrev(b) for b in row.sym_busses) if row.sym_busses else "·"


def _sweep_plain(rows, group, block, abbrev) -> str:
    out = [f"# {group}/{block}   {_FMT_LEGEND}"]
    pw = max((len(r.pass_name) for r in rows), default=4)
    out.append(f"{'NNN':>3} {'pass':<{pw}} f {'cons':>4} {'bus':>4} "
               f"{'mem':>3} {'der':>3} {'deg':>3} {'cols':>4}  sym-busses")
    for r in rows:
        out.append(
            f"{r.nnn:03d} {r.pass_name:<{pw}} {FMT_MARK.get(r.fmt, '?')} "
            f"{r.n_constraints:>4} {r.n_bus_interactions:>4} {r.n_memory:>3} "
            f"{r.n_derived_columns:>3} {r.max_degree:>3} "
            f"{r.distinct_columns:>4}  {_sym_cell(r, abbrev)}"
        )
    return "\n".join(out)


def _sweep_rich(rows, group, block, abbrev) -> str:
    from rich.console import Console
    from rich.table import Table

    console = Console()
    with console.capture() as cap:
        console.rule(f"[bold]{group}/{block}[/]   [dim]{_FMT_LEGEND}[/]")
        t = Table(show_edge=False)
        t.add_column("NNN", justify="right")
        t.add_column("pass")
        t.add_column("f", justify="center")
        t.add_column("cons", justify="right")
        t.add_column("bus", justify="right")
        t.add_column("mem", justify="right")
        t.add_column("der", justify="right")
        t.add_column("deg", justify="right")
        t.add_column("cols", justify="right")
        t.add_column("sym-busses")
        for r in rows:
            mark = FMT_MARK.get(r.fmt, "?")
            mark = f"[magenta]{mark}[/]" if r.fmt == "machine" else mark
            sym = _sym_cell(r, abbrev)
            sym = f"[yellow]{sym}[/]" if r.sym_busses else f"[dim]{sym}[/]"
            t.add_row(
                f"{r.nnn:03d}", r.pass_name, mark, str(r.n_constraints),
                str(r.n_bus_interactions), str(r.n_memory),
                str(r.n_derived_columns), str(r.max_degree),
                str(r.distinct_columns), sym,
            )
        console.print(t)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# sweep all (one row per block)
# --------------------------------------------------------------------------- #
def render_sweep_all(rows, group: str, sort: str, mode: str) -> str:
    if mode == JSON:
        return json.dumps(
            {"group": group, "sort": sort,
             "blocks": [r.as_dict() for r in rows]},
            indent=2,
        )
    if mode == RICH:
        return _sweep_all_rich(rows, group, sort)
    return _sweep_all_plain(rows, group, sort)


def _red_str(r) -> str:
    return "·" if r.reduction_pct is None else f"{r.reduction_pct}%"


def _sweep_all_plain(rows, group, sort) -> str:
    out = [f"# {group} · sort={sort} desc · {len(rows)} blocks"]
    out.append(f"{'block':>8} {'steps':>5} {'cons0':>6} {'consF':>5} "
               f"{'red%':>4} {'mem0':>4} {'memF':>4} {'degF':>4} "
               f"{'memSym':>6} {'othSym':>6} {'kb':>8}")
    for r in rows:
        out.append(
            f"{r.block:>8} {r.n_steps:>5} {r.cons0:>6} {r.consF:>5} "
            f"{_red_str(r):>4} {r.mem0:>4} {r.memF:>4} {r.max_degree_final:>4} "
            f"{('sym' if r.mem_sym_final else '·'):>6} "
            f"{('sym' if r.other_sym_final else '·'):>6} {r.kb0:>8.1f}"
        )
    return "\n".join(out)


def _sweep_all_rich(rows, group, sort) -> str:
    from rich.console import Console
    from rich.table import Table

    console = Console()
    with console.capture() as cap:
        console.rule(f"[bold]{group}[/]   [dim]sort={sort} desc · "
                     f"{len(rows)} blocks[/]")
        t = Table(show_edge=False)
        t.add_column("block", justify="right")
        for col in ("steps", "cons0", "consF", "red%", "mem0", "memF", "degF"):
            t.add_column(col, justify="right")
        t.add_column("memSym", justify="center")
        t.add_column("othSym", justify="center")
        t.add_column("kb", justify="right")

        def flag(on):
            return "[yellow]sym[/]" if on else "[dim]·[/]"

        for r in rows:
            t.add_row(
                r.block, str(r.n_steps), str(r.cons0), str(r.consF),
                _red_str(r), str(r.mem0), str(r.memF),
                str(r.max_degree_final), flag(r.mem_sym_final),
                flag(r.other_sym_final), f"{r.kb0:.1f}",
            )
        console.print(t)
    return cap.get().rstrip("\n")


# --------------------------------------------------------------------------- #
# subs (substitutions: var -> definition)
# --------------------------------------------------------------------------- #
def _expr_str(node) -> str:
    """Compact infix string for a (signed-normalized) expression tree."""
    if isinstance(node, list):
        if node and node[0] == "-" and len(node) == 2:
            return f"-{_expr_str(node[1])}"
        parts = [_expr_str(x) if i % 2 == 0 else str(x) for i, x in enumerate(node)]
        return "(" + " ".join(parts) + ")"
    return str(node)


def render_subs(subs, group: str, block: str, mode: str) -> str:
    """Render substitutions (already constant-normalized) var = definition."""
    if mode == JSON:
        return json.dumps(
            {"group": group, "block": block,
             "substitutions": [{"var": v, "def": d} for v, d in subs]},
            indent=2,
        )
    if mode == RICH:
        from rich.console import Console
        from rich.table import Table

        console = Console()
        with console.capture() as cap:
            console.rule(f"[bold]{group}/{block}[/] substitutions "
                         f"[dim]({len(subs)})[/]")
            t = Table(show_edge=False)
            t.add_column("variable", style="green")
            t.add_column("=")
            t.add_column("definition")
            for v, d in subs:
                t.add_row(str(v), "=", _expr_str(d))
            console.print(t)
        return cap.get().rstrip("\n")
    out = [f"# {group}/{block} substitutions ({len(subs)})"]
    out += [f"{v} = {_expr_str(d)}" for v, d in subs]
    return "\n".join(out)


# --------------------------------------------------------------------------- #
# diff (constraint-level)
# --------------------------------------------------------------------------- #
def _signed_str(c) -> str:
    from .normalize import normalize_constants
    return _expr_str(normalize_constants(c))


def _capped(items, limit):
    """Yield up to `limit` items; returns (shown_list, n_truncated)."""
    if limit is None or len(items) <= limit:
        return items, 0
    return items[:limit], len(items) - limit


def _group(strs):
    """Collapse identical strings to ordered (str, count) pairs."""
    out, counts = [], {}
    for s in strs:
        if s not in counts:
            counts[s] = 0
            out.append(s)
        counts[s] += 1
    return [(s, counts[s]) for s in out]


def _xn(count) -> str:
    return f"  (x{count})" if count > 1 else ""


def render_diff(diff, ta: Target, tb: Target, mode: str, limit: int = 20) -> str:
    if mode == JSON:
        return json.dumps({
            "a": vars(ta), "b": vars(tb), "format": diff.fmt,
            "removed": [_signed_str(c) for c in diff.removed],
            "added": [_signed_str(c) for c in diff.added],
            "changed": [{"before": _signed_str(x), "after": _signed_str(y)}
                        for x, y in diff.changed],
            "columns": {
                "added": [{"name": n, "def": _signed_str(d) if d is not None else None}
                          for n, d in diff.cols_added],
                "removed": [{"name": n, "def": _signed_str(d) if d is not None else None}
                            for n, d in diff.cols_removed],
            },
        }, indent=2)
    if mode == RICH:
        return _diff_rich(diff, ta, tb, limit)
    return _diff_plain(diff, ta, tb, limit)


def _diff_reassoc_hint(diff) -> bool:
    return bool(diff.changed and not diff.removed and not diff.added
                and diff.fmt == "machine")


def _diff_plain(diff, ta, tb, limit) -> str:
    out = [
        f"# A: {ta.group}/{ta.block} {ta.label} [{diff.fmt}]",
        f"# B: {tb.group}/{tb.block} {tb.label} [{diff.fmt}]",
        f"# constraints: -{len(diff.removed)} +{len(diff.added)} "
        f"~{len(diff.changed)}   columns: +{len(diff.cols_added)} "
        f"-{len(diff.cols_removed)}",
    ]
    if _diff_reassoc_hint(diff):
        out.append("# note: all changes are reassociations (likely loop_iteration)")
    changed = _group([f"{_signed_str(x)}  =>  {_signed_str(y)}"
                      for x, y in diff.changed])
    shown, trunc = _capped(changed, limit)
    for s, n in shown:
        out.append(f"~ {s}{_xn(n)}")
    if trunc:
        out.append(f"~ (+{trunc} more)")
    shown, trunc = _capped(_group([_signed_str(c) for c in diff.removed]), limit)
    for s, n in shown:
        out.append(f"- {s}{_xn(n)}")
    if trunc:
        out.append(f"- (+{trunc} more)")
    shown, trunc = _capped(_group([_signed_str(c) for c in diff.added]), limit)
    for s, n in shown:
        out.append(f"+ {s}{_xn(n)}")
    if trunc:
        out.append(f"+ (+{trunc} more)")
    for n, d in diff.cols_added:
        out.append(f"+col {n}" + (f" = {_signed_str(d)}" if d is not None else ""))
    for n, d in diff.cols_removed:
        out.append(f"-col {n}" + (f" = {_signed_str(d)}" if d is not None else ""))
    return "\n".join(out)


def _diff_rich(diff, ta, tb, limit) -> str:
    from rich.console import Console

    console = Console()
    with console.capture() as cap:
        console.rule(f"[bold]A[/] {ta.group}/{ta.block} {ta.label} "
                     f"[magenta]({diff.fmt})[/]   "
                     f"[bold]B[/] {tb.group}/{tb.block} {tb.label}")
        console.print(
            f"constraints: [red]-{len(diff.removed)}[/] "
            f"[green]+{len(diff.added)}[/] [yellow]~{len(diff.changed)}[/]   "
            f"columns: [green]+{len(diff.cols_added)}[/] "
            f"[red]-{len(diff.cols_removed)}[/]")
        if _diff_reassoc_hint(diff):
            console.print("[dim]all changes are reassociations "
                          "(likely loop_iteration)[/]")
        changed = _group([f"{_signed_str(x)}  [dim]=>[/]  {_signed_str(y)}"
                          for x, y in diff.changed])
        shown, trunc = _capped(changed, limit)
        for s, n in shown:
            console.print(f"[yellow]~[/] {s}{_xn(n)}")
        if trunc:
            console.print(f"[yellow]~ (+{trunc} more)[/]")
        shown, trunc = _capped(_group([_signed_str(c) for c in diff.removed]), limit)
        for s, n in shown:
            console.print(f"[red]-[/] {s}{_xn(n)}")
        if trunc:
            console.print(f"[red]- (+{trunc} more)[/]")
        shown, trunc = _capped(_group([_signed_str(c) for c in diff.added]), limit)
        for s, n in shown:
            console.print(f"[green]+[/] {s}{_xn(n)}")
        if trunc:
            console.print(f"[green]+ (+{trunc} more)[/]")
        for n, d in diff.cols_added:
            console.print(f"[green]+col[/] {n}"
                          + (f" = {_signed_str(d)}" if d is not None else ""))
        for n, d in diff.cols_removed:
            console.print(f"[red]-col[/] {n}"
                          + (f" = {_signed_str(d)}" if d is not None else ""))
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
  sweep   <group> <block> [--from N] [--to N]   per-step trail, 1 row/step
  sweep   all [<group>] [--sort KEY]   1 row PER BLOCK (group auto-picked
            if only one). KEY: cons0(default) consF steps mem0 memF size red
  subs    <group> <block>   list var -> definition (signed-normalized)
  diff    <group> <block> <stepA> <stepB> [--limit N]   constraint-level
            diff (removed/added/changed + columns). SAME representation only:
            refuses M-vs-C (the encoding flip is not a real change).

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

FORMAT (powdr emits three artifacts; lens auto-detects)
  machine        SymbolicMachine/AlgebraicExpression: uses real - and unary
                 ["-",e]; negatives signed. The _000_unopt base dump (has
                 block/subs) AND the outer steps (loop_iteration, inlining,
                 range_constraints, post-inline rule_based/trivial_simp).
  constraints    ConstraintSystem/GroupedExpression: NO -; negatives are
                 field residues (2013265920=p-1). The inner passes.
  substitutions  the _substitutions.json list of [var, definition] pairs.
  discriminator: any - operator => machine; else residue => constraints.
  normalization: constants are signed toward negative, p=2013265921
  (2013265920 -> -1). `lens subs` prints definitions in this form.
  comparing across encodings flags operator-delta artifacts.

JSON FIELDS (show)
  target{group,block,label,path}  format:"machine"|"constraints"
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

SWEEP COLUMNS / JSON (one row per step)
  NNN pass  f  cons bus mem der deg cols  sym-busses
  f = format marker: M=machine C=constraints
  cons=n_constraints bus=n_bus_interactions mem=Memory-bus count
  der=n_derived_columns deg=max degree cols=distinct columns
  sym-busses = abbreviated labels of busses with symbolic mult, else ·
  JSON: {group,block,steps:[{nnn,pass,format,n_constraints,
    n_bus_interactions,n_memory,n_derived_columns,max_degree,
    distinct_columns,sym_busses[]}]}

SWEEP ALL COLUMNS / JSON (one row per block, sorted by KEY desc)
  block steps cons0 consF red% mem0 memF degF memSym othSym kb
  cons0/consF=initial/final n_constraints  red%=reduction
  mem0/memF=initial/final Memory-bus count  degF=final max degree
  memSym=Memory bus has symbolic mult in final dump (special-cased)
  othSym=any non-Memory bus symbolic in final  kb=initial dump size
  JSON: {group,sort,blocks:[{block,n_steps,cons0,consF,reduction_pct,
    mem0,memF,max_degree_final,mem_sym_final,other_sym_final,kb0,bytes0}]}

EXAMPLES
  lens show keccak 2106412 011 --json
  lens show keccak 2106412 memory --plain
  lens compare keccak 2103924 010 011
  lens compare keccak 2103924 memory remove_free --json
  lens sweep keccak 2099512
  lens sweep keccak 2099512 --from 11 --to 23 --json
  lens sweep all
  lens sweep all keccak --sort consF --json
  lens subs keccak 2099512
  lens diff keccak 2104492 003 004
  lens diff keccak 2104492 010 011 --json

DIFF JSON FIELDS
  a{..} b{..} format  removed[str] added[str] changed[{before,after}]
  columns{added:[{name,def}], removed:[{name,def}]}
  same-representation only; M-vs-C diff exits non-zero with a message.
"""
