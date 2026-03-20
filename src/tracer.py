import logging
import sys

from .report.dumpers import Action
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, open_file
from .smt.conversion import SmtConverter
from .smt.utils import *


def trace():
    """Encode to check for a satisfying trace of the given dump."""

    filename = ARGS().input
    input = load_apc_dump(filename)
    out_core = filename.parent / f"trace-{filename.stem}.core.smt2"
    out_derived = filename.parent / f"trace-{filename.stem}.derived.smt2"

    with Action("tracer") as action:
        action += {"outputs": [out_core, out_derived]}
        with action.action("encode"):
            with SmtConverter(None, BasicBlock(input["block"])) as conv:
                formula = conv.to_formula_with_axioms(input)

        with action.action("out-core"):
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

        with action.action("out-derived"):
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

        return action
