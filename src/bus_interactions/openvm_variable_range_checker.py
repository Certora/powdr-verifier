"""Single-variable range checker: constrain ``x < 2**bits`` for small bit widths."""
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *
from ..utils.utils import none_if


class OpenVMVariableRangeCheckerEncoder(SingleInteractionEncoder):
    """
    Encodes variable range checker bus interactions. It constrains the value to
    be below `2^bits`, and we generally assume `bits <= 25`.
    """

    NAME = "variable range checker"

    @none_if(lambda: ARGS().no_varrange)
    def encode_pointwise(self, mult: Any, x: Any, bits: Any) -> FNode:
        """Constrain `x` to be in [0, 2^bits) when the interaction is enabled."""
        curbits = 25
        if bits.is_int_constant() and bits.constant_value() <= 25:
            curbits = bits.constant_value()
        
        x = wrap_mod(x)

        if mult.is_int_constant() and mult.constant_value() != 0:
            return LT(x, Int(2**curbits))

        return Implies(
            Not(field_eq(mult)),
            LT(x, Int(2**curbits)),
        )
