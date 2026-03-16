import sympy

from .conversion import to_sympy, to_smt
from .rewrites import rewrite_eqmod, rewrite_mod, rewrite_simplify, rewrite_z3simplify
from .rewrites_sympy import rewrite_choice, rewrite_mod_equality

from ..smt.utils import *

logger = logging.getLogger(__name__)

REWRITES = {
    operators.EQUALS: [rewrite_eqmod], # rewrite_z3simplify
    operators.MOD: [rewrite_mod],
}
REWRITES_SYMPY = {
    operators.EQUALS: [rewrite_choice],
}
MAX_REWRITE_COUNT = 5


@simple_profile
def rewrite_one(node_type: int, args: list[FNode], rewrites) -> FNode:
    """Apply the first matching rewrite rule to a single SymPy node."""
    for r in rewrites:
        res = r(node_type, args)
        if res is not None:
            return res
    return None


@simple_profile
def rewrite_one_sympy(node: sympy.Expr, rewrites) -> sympy.Expr:
    """Apply the first matching rewrite rule to a single SymPy node."""
    for r in rewrites:
        res = r(node)
        if res is not None:
            return res
    return None


class RelationRewriter(substituter.Substituter):
    def __init__(self, env=None):
        """Create a PySMT substituter that may rewrite equalities via SymPy."""
        substituter.Substituter.__init__(self, env=env)

    @substituter.handles(
        set(operators.ALL_TYPES) - frozenset([operators.EQUALS, operators.MOD])
    )
    def walk_identity(self, formula, args, **kwargs):
        """Rebuild non-equality nodes unchanged, preserving any attached comment."""
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.EQUALS, operators.MOD]))
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """Try to rewrite equality formulas (modulo field) via SymPy, otherwise keep them."""
        op = formula.node_type()
        if op in REWRITES:
            res = rewrite_one(op, args, REWRITES[formula.node_type()])
            if res is not None and res != formula:
                logger.debug(f"rewrote {formula} --> {res}")
                return keep_comment(res, formula)
        if op in REWRITES_SYMPY:
            try:
                node = get_env().formula_manager.create_node(op, tuple(args))
                res = to_smt(
                    rewrite_one_sympy(
                        to_sympy(node), REWRITES_SYMPY[formula.node_type()]
                    )
                )
            except AssertionError:
                res = formula
            except sympy.SympifyError:
                res = formula
            except Exception as e:
                logger.error(f"error rewriting {formula}: {e}")
                raise e
            if res != formula:
                logger.debug(f"rewrote sympy {formula} --> {res}")
                return keep_comment(res, formula)
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )


@simple_profile
def rewrite(input: FNode) -> FNode:
    """Rewrite a formula (or list of formulas) by repeatedly applying equality rewrites."""
    if ARGS().skip_rewriting:
        return input
    if isinstance(input, list):
        return [rewrite(i) for i in input]
    relation_rewriter = RelationRewriter()
    last = input
    next = None
    for _ in range(MAX_REWRITE_COUNT):
        next = relation_rewriter.substitute(last)
        if last == next:
            break
        last = next
    return last
