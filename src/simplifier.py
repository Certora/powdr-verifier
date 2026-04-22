import logging

from .report.action import Action
from .smt.utils import *
from .smt_backends.pysmt import pretty_print_smtlib, serialize_smtlib
from .utils.args import ARGS
from .utils.io import open_file

from .simplify import check_isqf, simplify_cvc5, simplify_demod, simplify_intervals, simplify_intervals2, simplify_z3, simplify_rewrite, simplify_model, simplify_andify, simplify_lift_forall, simplify_nnf


def simplify():
    """Read SMT2, run selected simplification passes, and write to output (or overwrite input)."""

    with Action("simplifier") as action:
        action += {
            "inputs": [ARGS().input],
            "outputs": [ARGS().output],
        }
        with action.action("load"):
            with open_file(ARGS().input, "r") as f:
                parser = SmtLibParser()
                logging.info(f"loading from {f.name}")
                smt_script = parser.get_script(f)

        dump_pretty = False
        for t in ARGS().tactic.split(":"):
            dump_pretty = False
            logging.info(f"simplifying with {t}")
            with action.action(t) as subaction:
                t,*args = t.split("-", 1)
                match t:
                    case "andify":
                        smt_script = simplify_andify(smt_script)
                    case "nnf":
                        smt_script = simplify_nnf(smt_script)
                    case "lift":
                        smt_script = simplify_lift_forall(smt_script)
                    case "rewrite":
                        smt_script = simplify_rewrite(smt_script)
                    case "demod":
                        smt_script = simplify_demod(smt_script)
                    case "intervals":
                        smt_script = simplify_intervals(smt_script)
                    case "intervals2":
                        smt_script = simplify_intervals2(smt_script)
                    case "cvc5":
                        smt_script = simplify_cvc5(smt_script)
                    case "z3":
                        smt_script = simplify_z3(smt_script, args)
                    case "model":
                        smt_script = simplify_model(smt_script)
                    case "isqf":
                        subaction += { "expected": "qf" }
                        if not check_isqf(smt_script):
                            logging.warning("formula is not quantifier-free")
                            subaction += { "result": "not-qf" }
                        else:
                            subaction += { "result": "qf" }
                    case "pretty" | "p":
                        dump_pretty = True
                    case _:
                        logging.error(f"ignoring unknown tactic: {t}")

        with action.action("dump"):
            with open_file(ARGS().output, "w") as out:
                logging.info(f"dumping formula to {out.name}")
                if dump_pretty:
                    pretty_print_smtlib(smt_script, out)
                else:
                    serialize_smtlib(smt_script, out)
        return action
