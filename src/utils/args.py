"""Global CLI namespace, subcommands, and accessors used across verifier entrypoints."""
import argparse
import logging
from pathlib import Path
from typing import Optional

from .enums import BusInteractionHandlers, FieldTypes, MemoryPresolve, XOrEncoding

__ARGS: Optional[argparse.Namespace] = None

def __build_parser(skip_subparsers=False):
    """Build the command line parser."""

    parser = argparse.ArgumentParser()
    parser.add_argument("-v", action="count", default=0)
    parser.add_argument("-vv", action="count", default=0)
    parser.add_argument("-V", action="append", nargs="?", default=[])
    parser.add_argument("-VV", action="append", nargs="?", default=[])
    parser.add_argument(
        "--bus-interaction-handler",
        type=BusInteractionHandlers,
        default=BusInteractionHandlers.DEFAULT,
        choices=list(BusInteractionHandlers),
    )
    parser.add_argument(
        "--field-type",
        type=FieldTypes,
        default=FieldTypes.BABYBEAR,
        choices=list(FieldTypes),
    )
    parser.add_argument(
        "--xor",
        type=XOrEncoding,
        default=XOrEncoding.AXIOMS,
        choices=list(XOrEncoding),
    )
    parser.add_argument("--skip-memory-analysis", action="store_true")
    parser.add_argument("--skip-range-inference", action="store_true")
    parser.add_argument("--use-memory-order", action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument(
        "--memory-encoding",
        type=str,
        choices=["array", "busat", "plain", "interface", "none"],
        default="plain",
    )
    parser.add_argument(
        "--bitwise-lift-axioms", action=argparse.BooleanOptionalAction, default=True
    )
    parser.add_argument(
        "--interface-limb-split", action=argparse.BooleanOptionalAction, default=True
    )
    parser.add_argument(
        "--interface-assume-bytes", action=argparse.BooleanOptionalAction, default=True
    )
    parser.add_argument(
        "--memory-presolve",
        type=MemoryPresolve,
        default=MemoryPresolve.NONE,
        choices=list(MemoryPresolve),
    )
    parser.add_argument("--dump-smt", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--base-dump", type=Path, default=None)
    parser.add_argument("--substitutions", type=Path, default=None)
    parser.add_argument("--solver", type=str, default="z3-nightly")
    parser.add_argument("--skip-rewriting", action="store_true")
    parser.add_argument("--with-sympy", action="store_true")
    parser.add_argument("--elim-with-model", type=Path, default=None)
    parser.add_argument("--cprofile", action="store_true")
    parser.add_argument("--no-typecheck", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument(
        "--default-executor",
        type=str,
        choices=["p", "r"],
        default="r",
        metavar="EXEC",
        help="default simplifier backend: p=python, r=rust",
    )
    parser.add_argument("--stats-run-id", type=str, default=None, metavar="RUN_ID")
    parser.add_argument("--stats-tag", type=str, default=None)

    parser.add_argument("--no-memory", action="store_true")
    parser.add_argument("--no-bitwise", action="store_true")
    parser.add_argument("--no-bridge", action="store_true")
    parser.add_argument("--no-pclookup", action="store_true")
    parser.add_argument("--no-varrange", action="store_true")
    parser.add_argument("--no-tuprange", action="store_true")

    if skip_subparsers:
        return parser

    sub = parser.add_subparsers(dest="command")

    sub_trace = sub.add_parser("trace")
    sub_trace.add_argument("input", type=Path)
    sub_trace.add_argument("output", type=Path, nargs="?")

    sub_eval = sub.add_parser("eval")
    sub_eval.add_argument("input", type=Path)
    sub_eval.add_argument("model", type=Path)

    sub_visualize = sub.add_parser("visualize")
    sub_visualize.add_argument("input", type=Path)
    sub_visualize.add_argument("model", type=Path)
    sub_visualize.add_argument("bus", type=str, nargs="*")
    sub_visualize.add_argument("--var-prefix", type=str, default=None)

    sub_diff = sub.add_parser("diff")
    sub_diff.add_argument("input_before", type=Path)
    sub_diff.add_argument("input_after", type=Path)
    sub_diff.add_argument(
        "--format", type=str, choices=["text", "json"], default="text"
    )
    sub_diff.add_argument("--with-encoding", action="store_true")
    sub_diff.add_argument("--with-model", type=Path)
    sub_diff.add_argument("--with-before-model", type=Path)
    sub_diff.add_argument("--with-after-model", type=Path)
    sub_diff.add_argument("--only-simplified", action="store_true")
    sub_diff.add_argument("--inject", nargs="?", default=None, const="random", metavar="SEED")

    sub_text = sub.add_parser("text")
    sub_text.add_argument("input", type=Path)

    sub_simplify = sub.add_parser("simplify")
    sub_simplify.add_argument("input", type=Path)
    sub_simplify.add_argument("tactic", type=str)
    sub_simplify.add_argument("output", type=Path)
    sub_simplify.add_argument("--timeout", type=float, default=60.0, metavar="SEC")
    sub_simplify.add_argument("--dump-steps", action="store_true")
    sub_simplify.add_argument("--with-model", type=Path)
    sub_simplify.add_argument("--optimization-step", type=str, default=None, metavar="PASS")

    sub_verify = sub.add_parser("verify")
    sub_verify.add_argument("input_before", type=Path)
    sub_verify.add_argument("input_after", type=Path)
    sub_verify.add_argument("output", type=Path)
    sub_verify.add_argument("--optimization-step", type=str, default=None, metavar="PASS")
    sub_verify.add_argument("--inject", nargs="?", default=None, const="random", metavar="SEED")
    sub_verify.add_argument("--skip-soundness", action="store_true")
    sub_verify.add_argument("--skip-completeness", action="store_true")
    sub_verify.add_argument("--skip-trivial", action="store_true")
    sub_verify.add_argument("--filter-constraints", action="store_true")

    sub_check = sub.add_parser("check")
    sub_check.add_argument("input", type=Path)
    sub_check.add_argument("--timeout", type=float, default=60.0, metavar="SEC")
    sub_check.add_argument("--dump-model", type=Path, default=None)
    sub_check.add_argument(
        "--solve-chunked", action=argparse.BooleanOptionalAction, default=True
    )
    sub_check.add_argument(
        "--solve-sliced", action=argparse.BooleanOptionalAction, default=False
    )
    sub_check.add_argument(
        "--boundary-regex",
        type=str,
        default=r"memory_(match|isinput|isoutput|isdisabled)",
        metavar="REGEX",
        help="variables matching this are the slice boundary (sliced mode)",
    )
    sub_check.add_argument("--sliced-arith-timeout", type=float, default=20.0, metavar="SEC")
    sub_check.add_argument("--sliced-mem-timeout", type=float, default=40.0, metavar="SEC")
    sub_check.add_argument("--sliced-full-timeout", type=float, default=60.0, metavar="SEC")
    sub_check.add_argument("--sliced-cegar-iters", type=int, default=3, metavar="N")
    sub_check.add_argument("--sliced-small-slice", type=int, default=500, metavar="N")
    sub_check.add_argument("--sliced-gc-factor", type=float, default=4.0, metavar="X")
    sub_check.add_argument(
        "--sliced-tactic",
        type=str,
        default=None,
        metavar="TACTIC",
        help="check-sat-using retry tactic on unknown ('' disables; default: "
        "simplify/propagate-values/solve-eqs/smt pipeline)",
    )
    sub_check.add_argument("--sliced-tactic-timeout", type=float, default=60.0, metavar="SEC")
    sub_check.add_argument("--sliced-closed-timeout", type=float, default=60.0, metavar="SEC")
    sub_check.add_argument(
        "--collect-unknowns",
        type=int,
        nargs="?",
        const=-1,
        default=None,
        metavar="N",
        help="sliced mode: continue past unknown disjuncts, recording up to N (-1 = all)",
    )
    sub_check.add_argument("--sliced-debug", action="store_true")
    sub_check.add_argument("--dump-slices", type=Path, default=None, metavar="DIR")
    sub_check.add_argument("--dump-slices-all", action="store_true")

    sub_aliasing = sub.add_parser("aliasing")
    sub_aliasing.add_argument("input", type=Path)

    sub_report = sub.add_parser("report")
    sub_report.add_argument("report_dir", type=Path)
    sub_report.add_argument("output", type=Path)

    sub_powdr_opt = sub.add_parser("powdr-opt")
    sub_powdr_opt.add_argument("input", type=Path)
    sub_powdr_opt.add_argument("opt_pass", type=str)
    sub_powdr_opt.add_argument("output", type=Path)
    sub_powdr_opt.add_argument("--base-dump", type=Path, default=None)

    return parser


def parse_args(args=None):
    """Parse the command line arguments."""
    parser = __build_parser()
    global __ARGS
    if args is None:
        __ARGS, _ = parser.parse_known_args([])
    else:
        __ARGS, extra = parser.parse_known_args(args)
        if extra:
            logging.info(f"unknown arguments: {" ".join(extra)}")

    ARGS().V = ARGS().V + 2 * ARGS().VV + ARGS().v * [""] + 2 * ARGS().vv * [""]
    def make_verbose(logger: logging.Logger):
        logger.setLevel(logger.getEffectiveLevel() - 10)
    for v in ARGS().V:
        if v is None or v == "":
            make_verbose(logging.root)
        else:
            make_verbose(logging.getLogger(f"src.{v}"))


def ARGS() -> argparse.Namespace:
    """Retrieve the command line arguments."""
    if __ARGS is None:
        parse_args()
    return __ARGS
