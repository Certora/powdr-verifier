"""Glue and small passes used by ``simplifier``: model substitution, QF check, rewrite."""
from ..utils.io import load_json
from ..smt.utils import *
from ..rewriter import rewrite

from .flatten_outer_array import simplify_flatten_outer_array
from .solve_eqs import simplify_solve_eqs
from .solve_store_eqs import simplify_solve_store_eqs
from .rewrite_store_eqs import simplify_rewrite_store_eqs
from .cvc5 import simplify_cvc5
from .bounds import simplify_bounds
from .demod import simplify_demod
from .intervals import simplify_intervals
from .z3 import simplify_z3
from .nnf import simplify_nnf
from .lift_forall import simplify_lift_forall
from .intervals import simplify_intervals2
from .bitwise import simplify_bitwise
from .mod_inv import simplify_mod_inv
from .skolem import simplify_skolem
from .normalize_eqs import simplify_normalize_eqs

def simplify_model(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Substitute concrete values from ``ARGS().with_model`` into asserted formulas (including ForAll)."""
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
        """Custom ``ForAll`` walk: substitute model values only into the inner matrix."""
        tmp = substituter.MGSubstituter(get_env())
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(subs, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
        qvars = [v for v in qvars if v not in substitutions]
        res = subs.mgr.ForAll(qvars, tmp.substitute(args[0], substitutions))
        return res

    subs.walk_forall = __walk_forall
    subs.functions[operators.FORALL] = __walk_forall

    changed = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            old = cmd.args[0]
            new = keep_comment(subs.substitute(old, substitutions), old)
            cmd.args[0] = new
            if new != old:
                changed += 1
    if subaction is not None:
        subaction += {"model_bindings": len(substitutions), "asserts_changed": changed}
    return smt_script


def simplify_evaluate(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Partially evaluate each assertion under an empty model (constant folding only)."""
    total = changed = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            total += 1
            old = cmd.args[0]
            cmd.args[0] = keep_comment(
                partial_evaluate(old, {}, {}),
                old,
            )
            changed += (cmd.args[0] != old)
    if subaction is not None:
        subaction += {"asserts_total": total, "asserts_changed": changed}
    return smt_script


def simplify_rewrite(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Rewrite each assertion independently with our internal rewriter."""
    changed = 0
    total = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            total += 1
            old = cmd.args[0]
            new = keep_comment(rewrite(old), old)
            cmd.args[0] = new
            if new != old:
                changed += 1
    if subaction is not None:
        subaction += {"asserts": total, "asserts_changed": changed}
    return smt_script

def check_isqf(smt_script: script.SmtLibScript) -> bool:
    """Return whether every asserted formula is quantifier-free per the environment QF oracle."""
    oracle = get_env().qfo
    for cmd in smt_script:
        if cmd.name == "assert":
            if not oracle.is_qf(cmd.args[0]):
                return False
    return True
