import logging
from pathlib import Path
import sys

from .smt_backends.pysmt import (
    FNode,
    SmtLibParser,
    pretty_print_smtlib,
    script,
)
from .utils.args import ARGS

from .simplify import simplify_cvc5, simplify_intervals, simplify_z3, simplify_rewrite


def simplify(
    input_path: Path,
    output_path: Path | None,
):
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""
    parser = SmtLibParser()
    logging.warning(f"loading from {input_path}")
    smt_script = parser.get_script_fname(str(input_path))

    for t in ARGS().tactic.split(":"):
        match t:
            case "rewrite":
                logging.warning(f"rewrite")
                smt_script = simplify_rewrite(smt_script)
            case "intervals":
                logging.warning(f"intervals")
                smt_script = simplify_intervals(smt_script)
            case "cvc5":
                logging.warning(f"cvc5")
                smt_script = simplify_cvc5(smt_script)
            case "z3":
                logging.warning(f"z3")
                smt_script = simplify_z3(smt_script)
            case _:
                logging.warning(f"ignoring unknown tactic: {t}")

    logging.warning(f"writing back")
    if output_path is None:
        output_path = input_path

    if str(output_path) == "-":
        pretty_print_smtlib(smt_script, sys.stdout)
    else:
        with output_path.open("w") as out:
            pretty_print_smtlib(smt_script, out)
