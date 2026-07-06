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

from . import align, certify, extract, meminfo, memstats, render, solve
from .busfmt import memory_bus_id
from .busmodel import memory_rows, symbolic_as_ordinals
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
                          help="address space to solve (default 1; symbolic-key "
                               "spaces like AS2 use the SMT engine, aliasing open)")
    sp_solve.add_argument("--assume-is-valid", dest="assume_is_valid",
                          action=argparse.BooleanOptionalAction, default=True,
                          help="assume the openvm activation selector is_valid==1 "
                               "(default on; only affects the final exported APC)")

    sp_ex = sub.add_parser("extract", parents=[common],
                           help="emit busat .bus (abstract timestamp order)")
    _circuit_a_args(sp_ex)
    sp_ex.add_argument("step_b", nargs="?",
                       help="second pass of the same block -> extract the REMOVED set")
    sp_ex.add_argument("--file-b", dest="file_b", help="explicit JSON for circuit B")
    sp_ex.add_argument("--as", dest="addr_space", type=int,
                       help="restrict to this address space")
    sp_ex.add_argument("-o", "--output", help="write .bus here (default stdout)")
    sp_ex.add_argument("--assume-is-valid", dest="assume_is_valid",
                       action=argparse.BooleanOptionalAction, default=True,
                       help="assume the openvm activation selector is_valid==1 "
                            "(default on; only affects the final exported APC)")

    sp_al = sub.add_parser("align", parents=[common],
                           help="map before->after memory busses (removal); high confidence")
    _circuit_a_args(sp_al)
    sp_al.add_argument("step_b", nargs="?",
                       help="the AFTER pass of the same block (before has >= after)")
    sp_al.add_argument("--file-b", dest="file_b", help="explicit JSON for the after circuit")
    sp_al.add_argument("--as", dest="addr_space", type=int, default=1,
                       help="address space to align (default 1; AS2 removals are "
                            "justified via solve's forced matching)")
    sp_al.add_argument("--assume-is-valid", dest="assume_is_valid",
                       action=argparse.BooleanOptionalAction, default=True,
                       help="assume the openvm activation selector is_valid==1 (default on)")

    sp_cert = sub.add_parser(
        "certify", parents=[common],
        help="emit (and optionally run) an SMT certificate per extracted fact")
    _circuit_a_args(sp_cert)
    sp_cert.add_argument("--run", action="store_true",
                         help="run each certificate through z3 (expect unsat)")
    sp_cert.add_argument("--z3-path", dest="z3_path",
                         help="z3 binary to use with --run (default: z3 on PATH)")
    sp_cert.add_argument("-o", "--output-dir", dest="output_dir",
                         help="write cert_*.smt2 files into this directory")
    sp_cert.add_argument("--assume-is-valid", dest="assume_is_valid",
                         action=argparse.BooleanOptionalAction, default=True,
                         help="assume the openvm activation selector is_valid==1 (default on)")

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
    mem_id = memory_bus_id(labels)
    rows = meminfo.compute(data, mem_id, args.addr_space)
    total = len(rows)
    if args.limit and total > args.limit:
        rows = rows[:args.limit]
    symbolic_as = len(symbolic_as_ordinals(memory_rows(data, mem_id)))
    print(render.render_info(rows, t, mode, total, symbolic_as))


def _run_solve(args, mode):
    data, labels, t = _load_circuit(args.group, args.block, args.step,
                                    getattr(args, "file_a", None), args.root)
    sol = solve.compute(data, memory_bus_id(labels), args.addr_space, args.assume_is_valid)
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
    model = extract.build_dict(data_a, mem_id, args.addr_space, data_b,
                               args.assume_is_valid)
    if args.json:
        print(json.dumps(extract.extract_json(model), indent=2))
        return
    text = extract.format_bus(model)
    if args.output:
        Path(args.output).write_text(text)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        print(text)


def _run_align(args, mode):
    data_a, labels, tgt_a = _load_circuit(args.group, args.block, args.step,
                                          getattr(args, "file_a", None), args.root)
    if args.file_b:
        data_b, _, tgt_b = _load_circuit(None, None, None, args.file_b, args.root)
    elif args.step_b:
        data_b, _, tgt_b = _load_circuit(args.group, args.block, args.step_b, None, args.root)
    else:
        raise ValueError("align needs two circuits: <group> <block> <before> <after> "
                         "or --file-a / --file-b")
    al = align.compute(data_a, data_b, memory_bus_id(labels), args.addr_space,
                       args.assume_is_valid)
    print(render.render_align(al, tgt_a, tgt_b, mode))


def _run_certify(args, mode):
    data, labels, t = _load_circuit(args.group, args.block, args.step,
                                    getattr(args, "file_a", None), args.root)
    out_dir = None
    if args.output_dir:
        out_dir = Path(args.output_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
    results = certify.certify_dump(data, memory_bus_id(labels), args.assume_is_valid,
                                   run=args.run, out_dir=out_dir, z3_path=args.z3_path)
    if mode == JSON:
        print(json.dumps({"target": t.path, "certificates": results}, indent=2))
        return
    print(render.render_certify(results, t, run=args.run))
    if args.run and any(r.get("result") != "unsat" for r in results):
        raise ValueError("certify: some certificates did not come back unsat")


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
            _run_align(args, mode)
        elif args.command == "certify":
            _run_certify(args, mode)
    except resolve.ResolveError as e:
        print(f"membus: {e}", file=sys.stderr)
        return 2
    except ValueError as e:
        print(f"membus: {e}", file=sys.stderr)
        return 2
    return 0
