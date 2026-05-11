from ..utils.io import load_json
from ..smt.utils import *
from ..rewriter import rewrite

from .cvc5 import simplify_cvc5
from .bounds import simplify_bounds
from .demod import simplify_demod
from .intervals import simplify_intervals
from .z3 import simplify_z3
from .andify import simplify_andify
from .isolate import simplify_isolate
from .nnf import simplify_nnf
from .lift_forall import simplify_lift_forall
from .intervals import simplify_intervals2
from .xor import simplify_gxor, simplify_qxor
from .mod_inv import simplify_mod_inv
from .skolem import simplify_skolem

def simplify_model(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    assert ARGS().with_model is not None
    model = load_json(ARGS().with_model)
    substitutions = {}
    for name, value in model.items():
        if isinstance(value, bool):
            substitutions[Symbol(name, BOOL)] = Bool(value)
        elif isinstance(value, int):
            substitutions[Symbol(name, INT)] = Int(value)
    
    subs = substituter.MGSubstituter(get_env())
    def __walk_forall(formula, args, **kwargs):
        tmp = substituter.MGSubstituter(get_env())
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(subs, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
        qvars = [v for v in qvars if v not in substitutions]
        res = subs.mgr.ForAll(qvars, tmp.substitute(args[0], substitutions))
        return res

    subs.walk_forall = __walk_forall
    subs.functions[operators.FORALL] = __walk_forall

    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(
                subs.substitute(cmd.args[0], substitutions),
                cmd.args[0]
            )
    return smt_script

    
def simplify_rewrite(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Rewrite each assertion independently with our internal rewriter."""
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = rewrite(cmd.args[0])
    return smt_script

def check_isqf(smt_script: script.SmtLibScript) -> bool:
    oracle = get_env().qfo
    for cmd in smt_script:
        if cmd.name == "assert":
            if not oracle.is_qf(cmd.args[0]):
                return False
    return True
