import logging
import sys

from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, open_file
from .smt.conversion import SmtConverter
from .smt.utils import *


def trace():
    """Solve for a satisfying trace of the given dump and print the resulting model (if any)."""

    filename = ARGS().input
    input = load_apc_dump(filename)
    out_core = filename.parent / f"trace-{filename.stem}.core.smt2"
    out_derived = filename.parent / f"trace-{filename.stem}.derived.smt2"

    with SmtConverter(None, BasicBlock(input["block"])) as conv:
        formula = conv.to_formula_with_axioms(input)

    with open_file(out_core, "w") as dump:
        pretty_print_smtlib(
            convert_to_smt_script(
                And(
                    *formula.constraints,
                    *formula.axioms,
                ),
                status = "sat",
            ),
            dump
        )

    with open_file(out_derived, "w") as dump:
        pretty_print_smtlib(
            convert_to_smt_script(
                And(
                    *formula.constraints,
                    *formula.axioms,
                    Or(
                        *[Not(Equals(v, expr)) for v, expr in formula.derived.items()]
                    ),
                ),
                status = "unsat",
            ),
            dump
        )

    return { "outputs": [out_core, out_derived] }
