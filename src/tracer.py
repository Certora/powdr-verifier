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
    out_core = filename.parent / f"trace-{filename.stem}.core.smt2"
    out_derived = filename.parent / f"trace-{filename.stem}.derived.smt2"
    out_mult = filename.parent / f"trace-{filename.stem}.mult.smt2"
    out_multpairs = filename.parent / f"trace-{filename.stem}.mult-pairs.smt2"
    out_timestamps = filename.parent / f"trace-{filename.stem}.timestamps.smt2"

    with Action("tracer") as action:
        action += {"outputs": [out_core, out_derived]}
        with action.action("encode"):
            with SmtConverter(None, BasicBlock(input["block"])) as conv:
                formula = conv.to_formula_with_axioms(input)

        with action.action("out-core"):
            encode_to_file(out_core, encode_trace(formula))

        with action.action("out-derived"):
            encode_to_file(out_derived, encode_trace_satisfies_derived(formula))
        
        with action.action("out-mult"):
            encode_to_file(out_mult, encode_mult_is_zero_or_pmone(conv, formula))
        
        with action.action("out-mult-pairs"):
            encode_to_file(out_multpairs, encode_mult_in_pairs_if_stateful(conv, formula))

        with action.action("out-timestamps"):
            encode_to_file(out_timestamps, encode_timestamps_increase(conv, formula))

        return action
