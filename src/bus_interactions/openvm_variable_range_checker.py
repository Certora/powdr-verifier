from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *

class OpenVMVariableRangeCheckerEncoder(SingleInteractionEncoder):
    """
    Encodes variable range checker bus interactions. It constrains the value to
    be below `2^bits`, and we generally assume `bits <= 25`.
    """
    @attach_comment("VARIABLE RANGE CHECKER for {2} {3}")
    def encode(self, mult: Any, x: Any, bits: Any) -> FNode:
        curbits = 25
        if bits.is_int_constant() and bits.constant_value() <= 25:
            curbits = bits.constant_value()

        return Implies(
            Not(Equals(mult, Int(0))),
            And(LE(Int(0), x), LT(x, Int(2 ** curbits)))
        )
