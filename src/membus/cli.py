"""argparse front-end for membus: stats / info / extract (+ align stub).

Input is lens-style — ``<group> <block> <step>`` resolved via `lens.resolve` —
or explicit files via ``--file-a`` / ``--file-b``. Two-circuit commands take a
second pass of the same block as ``<stepB>`` (or ``--file-b``).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from src.lens import loader, resolve

from . import extract, meminfo, memstats, render, solve
from .busfmt import memory_bus_id
from .render import JSON, PLAIN, Target, default_mode


def _add_common(parser: argparse.ArgumentParser, suppress: bool) -> None:
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
        prog="membus",
        description="Examine / extract / align memory-bus interactions in powdr "
                    "APC dumps (bus id 1).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="examples:\n"
               "  membus stats keccak 2100224 022\n"
               "  membus info keccak 2100224 021 --as 2\n"
               "  membus solve keccak 2100224 022 --as 1\n"
               "  membus extract keccak 2100224 021 022 --as 2 -o as2.bus\n"
               "\nRun `membus --agent` for the agent-oriented guide.")
    p.add_argument("--agent", action="store_true",
                   help="print a dense agent-oriented usage guide and exit")
    _add_common(p, suppress=False)
    common = argparse.ArgumentParser(add_help=False)
    _add_common(common, suppress=True)

    sub = p.add_subparsers(dest="command")

    sp_stats = sub.add_parser("stats", parents=[common],
                              help="memory-bus statistics for one circuit")
    _circuit_a_args(sp_stats)

    sp_info = sub.add_parser("info", parents=[common],
                             help="per-interaction key / timestamp / order / alias class")
    _circuit_a_args(sp_info)
    sp_info.add_argument("--as", dest="addr_space", type=int,
                         help="restrict to this address space")
    sp_info.add_argument("--limit", type=int, default=0,
                         help="max interactions listed (default 0 = all)")

    sp_solve = sub.add_parser("solve", parents=[common],
                              help="solve the memory bus: inputs / outputs / data flow")
    _circuit_a_args(sp_solve)
    sp_solve.add_argument("--as", dest="addr_space", type=int, default=1,
                          help="address space to solve (default 1; v1 supports AS1 only)")

    sp_ex = sub.add_parser("extract", parents=[common],
                           help="emit busat .bus (abstract timestamp order)")
    _circuit_a_args(sp_ex)
    sp_ex.add_argument("step_b", nargs="?",
                       help="second pass of the same block -> extract the REMOVED set")
    sp_ex.add_argument("--file-b", dest="file_b", help="explicit JSON for circuit B")
    sp_ex.add_argument("--as", dest="addr_space", type=int,
                       help="restrict to this address space")
    sp_ex.add_argument("-o", "--output", help="write .bus here (default stdout)")

    sp_al = sub.add_parser("align", parents=[common],
                           help="(v2) align two circuits' memory busses")
    _circuit_a_args(sp_al)
    sp_al.add_argument("step_b", nargs="?")
    sp_al.add_argument("--file-b", dest="file_b")

    return p


def _circuit_a_args(sp: argparse.ArgumentParser) -> None:
    sp.add_argument("group", nargs="?")
    sp.add_argument("block", nargs="?")
    sp.add_argument("step", nargs="?")
    sp.add_argument("--file-a", dest="file_a", help="explicit JSON for circuit A")


def _mode(args: argparse.Namespace) -> str:
    if getattr(args, "json", False):
        return JSON
    if getattr(args, "plain", False):
        return PLAIN
    return default_mode()


def _load_circuit(group, block, step, file_override, root):
    """Return ``(data, labels, Target)`` for one circuit."""
    if file_override:
        p = Path(file_override)
        return loader.load(p), {}, Target("(file)", "(file)", p.name, str(p))
    if not (group and block and step):
        raise resolve.ResolveError("specify <group> <block> <step> or --file-a PATH")
    directory = resolve.group_dir(group, root)
    entries = resolve.index_block(directory, block)
    entry = resolve.resolve_step(entries, step)
    labels = loader.load_bus_map(resolve.base_dump_path(directory, block))
    target = Target(group, resolve.normalize_block(block), entry.label, str(entry.path))
    return loader.load(entry.path), labels, target


def _run_stats(args, mode):
    data, labels, t = _load_circuit(args.group, args.block, args.step,
                                    getattr(args, "file_a", None), args.root)
    st = memstats.compute(data, memory_bus_id(labels))
    print(render.render_stats(st, t, mode))


def _run_info(args, mode):
    data, labels, t = _load_circuit(args.group, args.block, args.step,
                                    getattr(args, "file_a", None), args.root)
    rows = meminfo.compute(data, memory_bus_id(labels), args.addr_space)
    total = len(rows)
    if args.limit and total > args.limit:
        rows = rows[:args.limit]
    print(render.render_info(rows, t, mode, total))


def _run_solve(args, mode):
    data, labels, t = _load_circuit(args.group, args.block, args.step,
                                    getattr(args, "file_a", None), args.root)
    sol = solve.compute(data, memory_bus_id(labels), args.addr_space)
    print(render.render_solve(sol, t, mode))


def _run_extract(args):
    data_a, labels, _ = _load_circuit(args.group, args.block, args.step,
                                      getattr(args, "file_a", None), args.root)
    data_b = None
    if args.file_b:
        data_b = loader.load(Path(args.file_b))
    elif args.step_b:
        data_b, _, _ = _load_circuit(args.group, args.block, args.step_b, None, args.root)
    mem_id = memory_bus_id(labels)
    model = extract.build_dict(data_a, mem_id, args.addr_space, data_b)
    if args.json:
        print(json.dumps(extract.extract_json(model), indent=2))
        return
    text = extract.format_bus(model)
    if args.output:
        Path(args.output).write_text(text)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        print(text)


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
        if args.command == "stats":
            _run_stats(args, mode)
        elif args.command == "info":
            _run_info(args, mode)
        elif args.command == "solve":
            _run_solve(args, mode)
        elif args.command == "extract":
            _run_extract(args)
        elif args.command == "align":
            print("membus: align is not yet implemented (v2)", file=sys.stderr)
            return 2
    except resolve.ResolveError as e:
        print(f"membus: {e}", file=sys.stderr)
        return 2
    except ValueError as e:
        print(f"membus: {e}", file=sys.stderr)
        return 2
    return 0
