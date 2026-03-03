import logging
import sys

from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, open_file
from .smt.conversion import SmtConverter
from .smt.utils import *


def trace():
    """Solve for a satisfying trace of the given dump and print the resulting model (if any)."""

    input = load_apc_dump(ARGS().input, 'input')

    with SmtConverter(None, BasicBlock(input["block"])) as conv:
        formula = conv.to_formula_with_axioms(input)

    smtlib = convert_to_smt_script(
        And(
            *formula.constraints,
            *formula.axioms,
        )
    )

    for v, expr in formula.derived.items():
        smtlib.add("echo", [f"\"verify derived solution: {v} = {expr}\""])
        smtlib.add("check-sat-assuming", [Equals(v, expr)])

    with open_file(ARGS().output, "w") as dump:
        logging.info(f"dumping formula to {dump.name}")
        pretty_print_smtlib(smtlib, dump)
