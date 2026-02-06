from pysmt.fnode import FNode
from ..utils.args import ARGS

from ..utils.profiling import simple_profile
from .utils import unpack_modeq


def rewrite_mod(node: FNode) -> FNode:
    if not node.is_mod():
        return None
    expr, modulus = node.args()
    if not expr.is_symbol():
        return None
    if not modulus.is_int_constant() or modulus.constant_value() != ARGS().field_type.value:
        return None
    return expr
