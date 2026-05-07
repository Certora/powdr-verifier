import logging

from .report.action import Action
from .smt.utils import *
from .smt_backends.pysmt import pretty_print_smtlib, serialize_smtlib
from .utils.args import ARGS
from .utils.io import open_file

from .simplify import (
    check_isqf,
    simplify_andify,
    simplify_bounds,
    simplify_cvc5,
    simplify_demod,
    simplify_gxor,
    simplify_intervals,
    simplify_intervals2,
    simplify_isolate,
    simplify_lift_forall,
    simplify_mod_inv,
    simplify_model,
    simplify_nnf,
    simplify_qxor,
    simplify_rewrite,
    simplify_witnesses,
    simplify_z3,
)


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
        for i, t in enumerate(ARGS().tactic.split(":"), start=1):
            raw_tactic = t
            logging.info(f"simplifying with {t}")
            with action.action(t) as subaction:
                t,*args = t.split("-", 1)
                match t:
                    case "andify":
                        smt_script = simplify_andify(smt_script)
                    case "bounds":
                        smt_script = simplify_bounds(smt_script)
                    case "nnf":
                        smt_script = simplify_nnf(smt_script)
                    case "isolate":
                        smt_script = simplify_isolate(smt_script)
                    case "lift":
                        smt_script = simplify_lift_forall(smt_script)
                    case "witness":
                        smt_script = simplify_witnesses(smt_script)
                    case "rewrite":
                        smt_script = simplify_rewrite(smt_script)
                    case "demod":
                        smt_script = simplify_demod(smt_script)
                    case "qxor":
                        smt_script = simplify_qxor(smt_script)
                    case "gxor":
                        smt_script = simplify_gxor(smt_script)
                    case "mod_inv":
                        smt_script = simplify_mod_inv(smt_script)
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
            if ARGS().dump_steps:
                output = ARGS().output
                stem = output.name[:-len(output.suffix)] if output.suffix else output.name
                dump_file = output.with_name(f"{stem}.{i:02d}.{raw_tactic}.smt2")
                with open_file(dump_file, "w") as out:
                    logging.info(f"dumping intermediate formula to {out.name}")
                    if dump_pretty:
                        pretty_print_smtlib(smt_script, out)
                    else:
                        serialize_smtlib(smt_script, out)

        with action.action("dump"):
            with open_file(ARGS().output, "w") as out:
                logging.info(f"dumping formula to {out.name}")
                if dump_pretty:
                    pretty_print_smtlib(smt_script, out)
                else:
                    serialize_smtlib(smt_script, out)
        return action
