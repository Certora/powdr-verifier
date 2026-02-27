from ..smt.utils import *
from ..rewriter import rewrite
from .intervals import IntervalICPEngine

from .cvc5 import simplify_cvc5
from .intervals import simplify_intervals
from .z3 import simplify_z3

def simplify_rewrite(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Rewrite each assertion independently with our internal rewriter."""
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = rewrite(cmd.args[0])
    return smt_script
