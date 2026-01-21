from sympy import Wild, Eq, Mod, Expr
from typing import Optional

def unpack_modeq(node: Expr) -> Optional[tuple[Expr, Expr]]:
    e = Wild("e")
    c = Wild("c")

    if m := node.match(Eq(Mod(e, c), 0)):
        return m[e], m[c]
    return None
