"""argparse front-end for lens: ``show`` and ``compare`` subcommands."""
import argparse
import sys
from pathlib import Path

from . import render, resolve
from .loader import load, load_bus_map
from .metrics import DumpDiff, DumpStats
from .normalize import normalize_constants
from .render import Target
from .sweep import build_sweep, build_sweep_all


def _add_common(parser: argparse.ArgumentParser, suppress: bool) -> None:
    """Output/root flags, shared so they work before or after the subcommand.

    On subparsers we default to SUPPRESS so an omitted flag doesn't clobber a
    value already set on the top-level parser.
    """
    default = argparse.SUPPRESS if suppress else None
    parser.add_argument("--root", type=Path, default=default,
                        help="dumps root directory (default: powdr-dumps)")
    mode = parser.add_mutually_exclusive_group()
    flag_default = argparse.SUPPRESS if suppress else False
    mode.add_argument("-p", "--plain", action="store_true", default=flag_default,
                      help="plain text output (no color); default when piped")
    mode.add_argument("--json", action="store_true", default=flag_default,
                      help="JSON output")


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="lens",
        description="Statistics over powdr APC JSON dumps. "
        "Run `lens --agent` for an agent-oriented usage guide.",
    )
    p.add_argument("--agent", action="store_true",
                   help="print a dense agent-oriented usage guide and exit")
    _add_common(p, suppress=False)

    common = argparse.ArgumentParser(add_help=False)
    _add_common(common, suppress=True)

    sub = p.add_subparsers(dest="command")

    sp_show = sub.add_parser("show", parents=[common],
                             help="statistics for one dump")
    sp_show.add_argument("group")
    sp_show.add_argument("block")
    sp_show.add_argument("step")

    sp_cmp = sub.add_parser("compare", parents=[common],
                            help="A->B deltas between two steps")
    sp_cmp.add_argument("group")
    sp_cmp.add_argument("block")
    sp_cmp.add_argument("step_a")
    sp_cmp.add_argument("step_b")

    sp_sweep = sub.add_parser(
        "sweep", parents=[common],
        help="per-step trail of one block, or 'all' for one row per block")
    # `sweep <group> <block>`  OR  `sweep all [<group>]`
    sp_sweep.add_argument("target", help="group, or the literal 'all'")
    sp_sweep.add_argument("arg", nargs="?",
                          help="block (single-block) or group (with 'all')")
    sp_sweep.add_argument("--from", dest="lo", type=int, default=None,
                          help="lowest step NNN to include (single-block)")
    sp_sweep.add_argument("--to", dest="hi", type=int, default=None,
                          help="highest step NNN to include (single-block)")
    sp_sweep.add_argument("--sort", default="cons0",
                          choices=["cons0", "consF", "steps", "mem0", "memF",
                                   "size", "red"],
                          help="sort key for 'all' (default cons0, desc)")

    sp_subs = sub.add_parser(
        "subs", parents=[common],
        help="list a block's variable substitutions (signed-normalized)")
    sp_subs.add_argument("group")
    sp_subs.add_argument("block")

    return p


def _mode(args: argparse.Namespace) -> str:
    if args.json:
        return render.JSON
    if args.plain:
        return render.PLAIN
    return render.default_mode()


def _stats_for(entry: resolve.StepEntry, directory: Path, block: str) -> DumpStats:
    labels = load_bus_map(resolve.base_dump_path(directory, block))
    return DumpStats.from_data(load(entry.path), labels)


def _run_sweep(args, mode: str) -> None:
    """Dispatch `sweep all [<group>]` vs `sweep <group> <block>`."""
    if args.target == "all":
        directory = (resolve.group_dir(args.arg, args.root) if args.arg
                     else resolve.sole_group_dir(args.root))
        group = directory.name.removeprefix("guest-")
        blocks = resolve.list_blocks(directory)
        if not blocks:
            raise resolve.ResolveError(f"no blocks under {directory}")
        labels = load_bus_map(resolve.base_dump_path(directory, blocks[0]))
        rows = build_sweep_all(directory, labels, args.sort)
        print(render.render_sweep_all(rows, group, args.sort, mode))
        return

    if args.arg is None:
        raise resolve.ResolveError("sweep <group> <block>: block is required "
                                   "(or use `sweep all`)")
    group, block = args.target, args.arg
    directory = resolve.group_dir(group, args.root)
    entries = resolve.index_block(directory, block)
    labels = load_bus_map(resolve.base_dump_path(directory, block))
    rows = build_sweep(entries, labels, args.lo, args.hi)
    print(render.render_sweep(rows, group, resolve.normalize_block(block), mode))


def _run_subs(args, mode: str) -> None:
    """`subs <group> <block>`: list var -> definition, constants signed."""
    directory = resolve.group_dir(args.group, args.root)
    path = resolve.substitutions_path(directory, args.block)
    if path is None:
        raise resolve.ResolveError(
            f"no substitutions file for block {resolve.normalize_block(args.block)}")
    raw = load(path)
    subs = [(v, normalize_constants(d)) for v, d in raw]
    print(render.render_subs(subs, args.group,
                             resolve.normalize_block(args.block), mode))


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    if args.agent:
        print(render.agent_guide())
        return 0
    if args.command is None:
        _build_parser().print_help()
        return 0

    mode = _mode(args)
    try:
        if args.command == "sweep":
            _run_sweep(args, mode)
            return 0

        if args.command == "subs":
            _run_subs(args, mode)
            return 0

        directory = resolve.group_dir(args.group, args.root)
        entries = resolve.index_block(directory, args.block)

        if args.command == "show":
            entry = resolve.resolve_step(entries, args.step)
            stats = _stats_for(entry, directory, args.block)
            target = Target(args.group, resolve.normalize_block(args.block),
                            entry.label, str(entry.path))
            print(render.render_show(stats, target, mode))

        elif args.command == "compare":
            ea = resolve.resolve_step(entries, args.step_a)
            eb = resolve.resolve_step(entries, args.step_b)
            sa = _stats_for(ea, directory, args.block)
            sb = _stats_for(eb, directory, args.block)
            bid = resolve.normalize_block(args.block)
            ta = Target(args.group, bid, ea.label, str(ea.path))
            tb = Target(args.group, bid, eb.label, str(eb.path))
            print(render.render_compare(DumpDiff(sa, sb), ta, tb, mode))

    except resolve.ResolveError as e:
        print(f"lens: {e}", file=sys.stderr)
        return 2
    return 0
