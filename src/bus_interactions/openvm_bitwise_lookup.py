import logging
from typing import Any, Optional

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *
from ..utils.enums import XOrEncoding
from ..utils.utils import none_if


class OpenVMBitwiseLookupEncoder(SingleInteractionEncoder):
    """
    Encodes bitwise lookup bus interactions. It implements two cases:

    * `(x, y, 0, 0)` constrains `x` and `y` to be bytes
    * `(x, y, z, 1)` constrains `x`, `y`, and `z` to be bytes and `z = x xor y`

    The xor is encoded as an overapproximating `uf_xor` that is restricted
    on a best-effort basis by some axioms.
    """

    UF_XOR = Symbol("uf_xor", FunctionType(INT, [INT, INT]))
    WRAP_XOR = lambda self, x, y: Ite(
        Equals(x, Int(0)), y,
        Ite(
            Equals(y, Int(0)), x,
            Ite(Equals(x, y), Int(0),
            Function(self.UF_XOR, [x, y]))
        )
    )
    interpreters = {
        UF_XOR: (
            lambda x, y: Int(x ^ y),
            lambda x, y: (
                y
                if x.is_zero()
                else (x if y.is_zero() else (Int(0) if x == y else None))
            ),
        ),
    }
    NAME = "bitwise lookup"

    def __init__(self) -> None:
        """Initialize the encoder and mark the `uf_xor` UF as a global symbol."""
        super().__init__()
        self.instantiations = set()
        self.needs_xor_axioms = False
        self.globals = frozenset([self.UF_XOR])
    
    def __XOR(self, x: Any, y: Any) -> FNode:
        match ARGS().xor:
            case XOrEncoding.GROUNDED:
                self.instantiations.add((x, y))
                return Function(self.UF_XOR, [x, y])
            case XOrEncoding.AXIOMS:
                self.needs_xor_axioms = True
                return Function(self.UF_XOR, [x, y])
            case XOrEncoding.WRAPPED_AXIOMS:
                self.needs_xor_axioms = True
                return self.WRAP_XOR(x, y)
            case XOrEncoding.WRAPPED_GROUNDED:
                self.instantiations.add((x, y))
                return self.WRAP_XOR(x, y)
            case _:
                raise ValueError(f"Unsupported XOR encoding: {ARGS().xor}")

    @none_if(lambda: ARGS().no_bitwise)
    def encode_pointwise(self, mult: Any, x: Any, y: Any, z: Any, op: Any) -> Optional[FNode]:
        """Encode byte-range constraints and XOR relation depending on `op`."""
        if op == Int(0) and z == Int(0):
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(
                    LE(Int(0), wrap_mod(x)),
                    LE(wrap_mod(x), Int(255)),
                    LE(Int(0), wrap_mod(y)),
                    LE(wrap_mod(y), Int(255)),
                    Equals(z, Int(0)),
                    Equals(op, Int(0)),
                ),
            )
        elif op == Int(1):
            self.needs_xor_axioms = True
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(
                    LE(Int(0), wrap_mod(x)),
                    LE(wrap_mod(x), Int(255)),
                    LE(Int(0), wrap_mod(y)),
                    LE(wrap_mod(y), Int(255)),
                    Equals(self.__XOR(wrap_mod(x), wrap_mod(y)), wrap_mod(z)),
                    Equals(op, Int(1)),
                ),
            )
        else:
            logging.error(f"Unsupported bitwise operation: {op}")
            return None

    @attach_comment("{0.NAME} axioms")
    def get_axioms(self) -> Iterable[FNode]:
        """Return basic axioms restricting `uf_xor` when XOR is used in any interaction."""
        match ARGS().xor:
            case XOrEncoding.AXIOMS:
                if self.needs_xor_axioms:
                    x = Symbol("x", INT)
                    y = Symbol("y", INT)
                    yield ForAll([x], Equals(Function(self.UF_XOR, [x, Int(0)]), x))
                    yield ForAll([x], Equals(Function(self.UF_XOR, [Int(0), x]), x))
                    yield ForAll([x], Equals(Function(self.UF_XOR, [x, x]), Int(0)))
                    yield ForAll([x,y], Implies(
                        Equals(Function(self.UF_XOR, [x, y]), x),
                        Equals(y, Int(0))
                    ))
                    yield ForAll([x,y], Implies(
                        Equals(Function(self.UF_XOR, [y, x]), x),
                        Equals(y, Int(0))
                    ))
            case XOrEncoding.GROUNDED:
                for x, y in self.instantiations:
                    term = Function(self.UF_XOR, [x, y])
                    if x == y:
                        yield Equals(term, Int(0))
                    else:
                        yield Iff(Equals(x, Int(0)), Equals(term, y))
                        yield Iff(Equals(y, Int(0)), Equals(term, x))
                        yield Iff(Equals(x, term), Equals(y, Int(0)))
                        yield Iff(Equals(y, term), Equals(x, Int(0)))
            case XOrEncoding.WRAPPED_AXIOMS | XOrEncoding.WRAPPED_GROUNDED:
                pass
            case _:
                raise ValueError(f"Unsupported XOR encoding: {ARGS().xor}")