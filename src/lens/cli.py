"""argparse front-end for lens: ``show`` and ``compare`` subcommands."""
import argparse
import sys
from pathlib import Path

from . import render, resolve
from .loader import load, load_bus_map
from .metrics import DumpDiff, DumpStats
from .render import Target


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
