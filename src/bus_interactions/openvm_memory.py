from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMMemoryEncoder(SingleInteractionEncoder):
    def encode(self, mult: Any, address_space: Any, pointer: Any, data: list[Any], timestamp: Any) -> FNode:
        return Implies(
            Equals(wrap_mod(mult), wrap_mod(Int(-1))),
            And(
                *[ And(LE(Int(0), d), LE(d, Int(255))) for d in data ]
            )
        )
