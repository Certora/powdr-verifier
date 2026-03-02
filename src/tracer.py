import json
import logging

from .rewriter import rewrite
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .smt.conversion import SmtConverter
from .smt.utils import *


def trace(input: dict):
    """Solve for a satisfying trace of the given dump and print the resulting model (if any)."""

    with SmtConverter(None, BasicBlock(input["block"])) as conv:
        formula = conv.to_formula_with_axioms(input)

    smtlib = convert_to_smt_script(
        And(
            *formula.constraints,
            *formula.axioms,
        ),
        AUFNIA
    )

    for v, expr in formula.derived.items():
        smtlib.add("echo", [f"verify derived solution: {v} = {expr}"])
        smtlib.add("check-sat-assuming", [Equals(v, expr)])

    filename = ARGS().input.parent / f"trace-{ARGS().input.stem}.smt2"
    logging.info(f"dumping formula to {filename}")
    with open(filename, "w") as dump:
        pretty_print_smtlib(smtlib, dump)
