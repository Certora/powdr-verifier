"""Small SymPy pattern helpers shared by ``rewrites_sympy``."""
from sympy import Integer, Wild, Eq, Mod, Expr
from typing import Optional

from ..utils.args import ARGS


def unpack_modeq(node: Expr) -> Optional[tuple[Expr, Expr]]:
    """If `node` is of the form `Eq(Mod(e, p), 0)` extract `(e, p)`, else return None."""
    e = Wild("e")
    c = Wild("c", properties=[lambda k: k == Integer(ARGS().field_type.value)])

    if m := node.match(Eq(Mod(e, c), 0)):
        return m[e], m[c]
    return None
