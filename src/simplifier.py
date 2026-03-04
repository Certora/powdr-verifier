import logging

from .smt.utils import *
from .utils.args import ARGS
from .utils.io import open_file

from .simplify import simplify_cvc5, simplify_intervals, simplify_z3, simplify_rewrite, simplify_model


def simplify():
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""

    with open_file(ARGS().input, "r") as f:
        parser = SmtLibParser()
        logging.info(f"loading from {f.name}")
        smt_script = parser.get_script(f)

    for t in ARGS().tactic.split(":"):
        match t:
            case "rewrite":
                logging.info(f"rewrite")
                smt_script = simplify_rewrite(smt_script)
            case "intervals":
                logging.info(f"intervals")
                smt_script = simplify_intervals(smt_script)
            case "cvc5":
                logging.info(f"cvc5")
                smt_script = simplify_cvc5(smt_script)
            case "z3":
                logging.info(f"z3")
                smt_script = simplify_z3(smt_script)
            case "model":
                logging.info(f"model")
                smt_script = simplify_model(smt_script)
            case _:
                logging.info(f"ignoring unknown tactic: {t}")

    with open_file(ARGS().output, "w") as out:
        logging.info(f"dumping formula to {out.name}")
        pretty_print_smtlib(smt_script, out)
