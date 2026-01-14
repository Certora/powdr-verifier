from .permutation_check import encode_permutation_check
from .single_interaction_encoder import SingleInteractionEncoder
from .sequencing import encode_sequencing

from ..smt_utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder):
    def __init__(self, name: str) -> None:
        super().__init__(name)
        self.interactions = []

    def encode(self, mult: FNode, pc: FNode, timestamp: FNode) -> FNode:
        self.interactions.append((mult, [pc, timestamp]))
        return TRUE()

    def get_axioms(self) -> list[FNode]:
        encode_timestamps = lambda i1, i2: LT(i1[1], i2[1])
        return encode_permutation_check(f'{self.name}_eb', self.interactions, encode_timestamps)
