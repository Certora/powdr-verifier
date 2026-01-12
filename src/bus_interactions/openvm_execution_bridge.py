from .single_interaction_encoder import SingleInteractionEncoder
from .sequencing import encode_sequencing

from ..smt_utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder):
    def __init__(self, name: str) -> None:
        super().__init__(name)
        self.interactions = []

    def encode(self, mult: FNode, pc: FNode, timestamp: FNode) -> FNode:
        self.interactions.append((pc, timestamp))
        return TRUE()

    def get_axioms(self) -> list[FNode]:
        return encode_sequencing(f'{self.name}_eb', self.interactions)
