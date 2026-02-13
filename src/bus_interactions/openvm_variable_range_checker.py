from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *


class OpenVMVariableRangeCheckerEncoder(SingleInteractionEncoder):
    """
    Encodes variable range checker bus interactions. It constrains the value to
    be below `2^bits`, and we generally assume `bits <= 25`.
    """

    NAME = "variable range checker"

    def encode_pointwise(self, mult: Any, x: Any, bits: Any) -> FNode:
        """Constrain `x` to be in [0, 2^bits) when the interaction is enabled."""
        curbits = 25
        if bits.is_int_constant() and bits.constant_value() <= 25:
            curbits = bits.constant_value()

        if not x.is_symbol():
            x = wrap_mod(x)

        if mult.is_int_constant() and mult.constant_value() != 0:
            return And(LE(Int(0), x), LT(x, Int(2**curbits)))

        return Implies(
            Not(Equals(wrap_mod(mult), Int(0))),
            And(LE(Int(0), x), LT(x, Int(2**curbits))),
        )
