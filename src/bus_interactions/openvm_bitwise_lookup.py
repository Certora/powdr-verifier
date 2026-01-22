import logging
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..utils.smt_utils import *

class OpenVMBitwiseLookupEncoder(SingleInteractionEncoder):
    """
    Encodes bitwise lookup bus interactions. It implements two cases:

    * `(x, y, 0, 0)` constrains `x` and `y` to be bytes
    * `(x, y, z, 1)` constrains `x`, `y`, and `z` to be bytes and `z = x xor y`

    The xor is encoded as an overapproximating `uf_xor` that is restricted
    on a best-effort basis by some axioms.
    """
    UF_XOR = Symbol('uf_xor', FunctionType(INT, [INT, INT]))
    interpreters = {
        UF_XOR: (
            lambda x,y: Int(x ^ y),
            lambda x,y: y if x.is_zero() else (x if y.is_zero() else (Int(0) if x == y else None))
        ),
    }

    def __init__(self) -> None:
        super().__init__()
        self.needs_xor_axioms = False
        self.globals = frozenset([self.UF_XOR])

    def encode(self, mult: Any, x: Any, y: Any, z: Any, op: Any) -> FNode:
        if op == Int(0) and z == Int(0):
            return with_comment(
                And(
                    LE(Int(0), x), LE(x, Int(255)),
                    LE(Int(0), y), LE(y, Int(255)),
                    Equals(z, Int(0)),
                    Equals(op, Int(0)),
                ),
                f"BITWISE LOOKUP {x} {y} {z} 0"
            )
        elif op == Int(1):
            self.needs_xor_axioms = True
            return with_comment(
                And(
                    LE(Int(0), x), LE(x, Int(255)),
                    LE(Int(0), y), LE(y, Int(255)),
                    Equals(Function(self.UF_XOR, [x, y]), z),
                    Equals(op, Int(1)),
                ),
                f"BITWISE LOOKUP {x} {y} {z} 1"
            )
        else:
            logging.error(f"Unsupported bitwise operation: {op}")
            return None

    def get_axioms(self) -> list[FNode]:
        if not self.needs_xor_axioms:
            return TRUE()
        x = Symbol('x', INT)
        return with_comment(
            And(
                ForAll([x], Equals(Function(self.UF_XOR, [x, Int(0)]), x)),
                ForAll([x], Equals(Function(self.UF_XOR, [Int(0), x]), x)),
                ForAll([x], Equals(Function(self.UF_XOR, [x, x]), Int(0))),
            ),
            f"BITWISE LOOKUP XOR AXIOMS"
        )
