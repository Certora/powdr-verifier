from .encoding import *
from .report.dumpers import Action
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump
from .smt.conversion import SmtConverter
from .smt.utils import *


def trace():
    """Encode to check for a satisfying trace of the given dump."""

    filename = ARGS().input
    input = load_apc_dump(filename)
    out_dir = ARGS().output.parent if ARGS().output is not None else filename.parent
    out_core = out_dir / f"trace-{filename.stem}.core.smt2"
    out_sanity = out_dir / f"trace-{filename.stem}.sanity.smt2"

    with Action("tracer") as action:
        action += {"outputs": [out_core, out_sanity]}
        with action.action("encode"):
            with SmtConverter(None, BasicBlock(input["block"])) as conv:
                formula = conv.to_formula_with_axioms(input)

        with action.action("out-core"):
            encode_to_file(out_core, encode_trace(formula))

        with action.action("out-sanity"):
            encode_to_file(out_sanity, encode_trace_sanity(conv, formula))

        return action
