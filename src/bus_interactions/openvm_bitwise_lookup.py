import logging
from typing import Any, Optional

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *

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
        """Initialize the encoder and mark the `uf_xor` UF as a global symbol."""
        super().__init__()
        self.needs_xor_axioms = False
        self.globals = frozenset([self.UF_XOR])

    @attach_comment("BITWISE LOOKUP {2} {3} {4} {5}")
    def encode(self, mult: Any, x: Any, y: Any, z: Any, op: Any) -> FNode:
        """Encode byte-range constraints and XOR relation depending on `op`."""
        if op == Int(0) and z == Int(0):
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(
                    LE(Int(0), x), LE(x, Int(255)),
                    LE(Int(0), y), LE(y, Int(255)),
                    Equals(z, Int(0)),
                    Equals(op, Int(0)),
                )
            )
        elif op == Int(1):
            self.needs_xor_axioms = True
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(
                    LE(Int(0), x), LE(x, Int(255)),
                    LE(Int(0), y), LE(y, Int(255)),
                    Equals(Function(self.UF_XOR, [x, y]), z),
                    Equals(op, Int(1)),
                )
            )
        else:
            logging.error(f"Unsupported bitwise operation: {op}")
            return None

    @attach_comment("BITWISE LOOKUP XOR AXIOMS")
    def get_axioms(self) -> Optional[FNode]:
        """Return basic axioms restricting `uf_xor` when XOR is used in any interaction."""
        if not self.needs_xor_axioms:
            return None
        x = Symbol('x', INT)
        return And(
            ForAll([x], Equals(Function(self.UF_XOR, [x, Int(0)]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [Int(0), x]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [x, x]), Int(0))),
        )
