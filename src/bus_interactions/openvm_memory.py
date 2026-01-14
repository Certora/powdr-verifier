from typing import Any

from .permutation_check import encode_permutation_check

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMMemoryEncoder(SingleInteractionEncoder):
    def __init__(self, name: str) -> None:
        super().__init__(name)
        self.interactions = {}
    
    def __add_interaction(self, mult: FNode, address_space: FNode, pointer: FNode, data: list[FNode], timestamp: FNode) -> None:
        assert address_space.is_int_constant() and pointer.is_int_constant()
        if (address_space, pointer) not in self.interactions:
            self.interactions[(address_space, pointer)] = []
        self.interactions[(address_space, pointer)].append((mult, data + [timestamp]))

    def encode(self, mult: FNode, address_space: FNode, pointer: FNode, data: list[FNode], timestamp: FNode) -> FNode:
        self.__add_interaction(mult, address_space, pointer, data, timestamp)
        return Implies(
            Equals(wrap_mod(mult), wrap_mod(Int(-1))),
            And(
                *[ And(LE(Int(0), d), LE(d, Int(255))) for d in data ]
            )
        )
    
    def get_axioms(self) -> list[FNode]:
        encode_timestamps = lambda i1, i2: LT(i1[4], i2[4])
        return And(
            encode_permutation_check(f'{self.name}_mem_{address_space}_{pointer}', interactions, encode_timestamps)
            for (address_space, pointer), interactions in self.interactions.items()
        )

