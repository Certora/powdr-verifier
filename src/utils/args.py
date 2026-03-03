import argparse
import logging
from pathlib import Path
from typing import Optional

from .bus_interaction_handlers import BusInteractionHandlers
from .field_types import FieldTypes

__ARGS: Optional[argparse.Namespace] = None


def parse_args(args=None):
    """Parse the command line arguments."""

    # first craft a parent parser so that the arguments are accepted before and after the command
    parent = argparse.ArgumentParser(add_help=False)
    parent.add_argument("-v", "--verbose", action="append", nargs="?", default=[])
    parent.add_argument("-vv", "--very-verbose", action="append", nargs="?", default=[])
    parent.add_argument(
        "--bus-interaction-handler",
        type=BusInteractionHandlers,
        default=BusInteractionHandlers.DEFAULT,
        choices=list(BusInteractionHandlers),
    )
    parent.add_argument(
        "--field-type",
        type=FieldTypes,
        default=FieldTypes.BABYBEAR,
        choices=list(FieldTypes),
    )
    parent.add_argument("--skip-memory-analysis", action="store_true")
    parent.add_argument("--memory-encoding", type=str, choices=["array", "busat"], default="array")
    parent.add_argument("--dump-smt", action="store_true")
    parent.add_argument("--check", action="store_true")
    parent.add_argument("--with-intervals", action="store_true", default=False)
    parent.add_argument("--base-dump", type=Path, default=None)
    parent.add_argument("--eliminations", type=Path, default=None)
    parent.add_argument("--solver", type=str, default="z3-latest")
    parent.add_argument("--skip-rewriting", action="store_true")
    parent.add_argument("--unroll-mod", action="store_true")
    parent.add_argument("--elim-with-skolem", action="store_true")
    parent.add_argument("--elim-with-model", type=Path, default=None)

    parser = argparse.ArgumentParser(parents=[parent])

    sub = parser.add_subparsers(dest="command")

    sub_trace = sub.add_parser("trace", parents=[parent])
    sub_trace.add_argument("input", type=Path)
    sub_trace.add_argument("output", type=Path, nargs="?")

    sub_eval = sub.add_parser("eval", parents=[parent])
    sub_eval.add_argument("input", type=Path)
    sub_eval.add_argument("model", type=Path)

    sub_diff = sub.add_parser("diff", parents=[parent])
    sub_diff.add_argument("input_before", type=Path)
    sub_diff.add_argument("input_after", type=Path)
    sub_diff.add_argument(
        "--format", type=str, choices=["text", "json"], default="text"
    )
    sub_diff.add_argument("--with-encoding", action="store_true")
    sub_diff.add_argument("--with-model", type=Path)
    sub_diff.add_argument("--only-simplified", action="store_true")

    sub_text = sub.add_parser("text", parents=[parent])
    sub_text.add_argument("input", type=Path)

    sub_simplify = sub.add_parser("simplify", parents=[parent])
    sub_simplify.add_argument("input", type=Path)
    sub_simplify.add_argument("tactic", type=str)
    sub_simplify.add_argument("output", type=Path, nargs="?")

    sub_verify = sub.add_parser("verify", parents=[parent])
    sub_verify.add_argument("input_before", type=Path)
    sub_verify.add_argument("input_after", type=Path)
    sub_verify.add_argument("output", type=Path, nargs="?")

    sub_check = sub.add_parser("check", parents=[parent])
    sub_check.add_argument("input", type=Path)
    sub_check.add_argument("--print-model", action="store_true")
    sub_check.add_argument("--dump-model", type=Path, default=None)

    sub_aliasing = sub.add_parser("aliasing", parents=[parent])
    sub_aliasing.add_argument("input", type=Path)

    global __ARGS
    if args is None:
        __ARGS, _ = parser.parse_known_args([])
    else:
        __ARGS, extra = parser.parse_known_args(args)
        if extra:
            logging.warning(f"unknown arguments: {" ".join(extra)}")
    
    ARGS().verbose = ARGS().verbose + 2 * ARGS().very_verbose
    def make_verbose(logger: logging.Logger):
        logger.setLevel(logger.getEffectiveLevel() - 10)
    for v in ARGS().verbose:
        if v is None:
            make_verbose(logging.root)
        else:
            make_verbose(logging.getLogger(f"src.{v}"))
    

def ARGS() -> argparse.Namespace:
    """Retrieve the command line arguments."""
    if __ARGS is None:
        parse_args()
    return __ARGS
