from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMVariableRangeCheckerEncoder(SingleInteractionEncoder):
    def encode(self, mult: Any, x: Any, bits: Any) -> FNode:
        curbits = 25
        if bits.is_int_constant() and bits.constant_value() <= 25:
            curbits = bits.constant_value()

        return And(
            LE(Int(0), x), LT(x, Int(2 ** curbits)),
        )
