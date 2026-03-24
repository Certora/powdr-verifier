import argparse
import logging
from pathlib import Path
from typing import Optional

from .enums import BusInteractionHandlers, FieldTypes, XOrEncoding

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
        default=XOrEncoding.DEFAULT,
        choices=list(XOrEncoding),
    )
    parser.add_argument("--skip-memory-analysis", action="store_true")
    parser.add_argument("--memory-encoding", type=str, choices=["array", "busat"], default="array")
    parser.add_argument("--dump-smt", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--base-dump", type=Path, default=None)
    parser.add_argument("--eliminations", type=Path, default=None)
    parser.add_argument("--solver", type=str, default="z3-latest")
    parser.add_argument("--skip-rewriting", action="store_true")
    parser.add_argument("--elim-with-skolem", action="store_true")
    parser.add_argument("--elim-with-model", type=Path, default=None)

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

    sub_text = sub.add_parser("text")
    sub_text.add_argument("input", type=Path)

    sub_simplify = sub.add_parser("simplify")
    sub_simplify.add_argument("input", type=Path)
    sub_simplify.add_argument("tactic", type=str)
    sub_simplify.add_argument("output", type=Path)
    sub_simplify.add_argument("--with-model", type=Path)

    sub_verify = sub.add_parser("verify")
    sub_verify.add_argument("input_before", type=Path)
    sub_verify.add_argument("input_after", type=Path)
    sub_verify.add_argument("output", type=Path)

    sub_check = sub.add_parser("check")
    sub_check.add_argument("input", type=Path)
    sub_check.add_argument("--dump-model", type=Path, default=None)

    sub_aliasing = sub.add_parser("aliasing")
    sub_aliasing.add_argument("input", type=Path)

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
            logging.warning(f"unknown arguments: {" ".join(extra)}")
    
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
