from .permutation_check import encode_permutation_check
from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder):
    """
    Encodes execution bridge bus interactions. It implements a permutation
    check on all interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        super().__init__()
        self.interactions = []

    def encode(self, mult: FNode, pc: FNode, timestamp: FNode) -> FNode:
        self.interactions.append((mult, [pc, timestamp]))
        return with_comment(TRUE(), f"EXECUTION BRIDGE")

    def get_axioms(self) -> list[FNode]:
        encode_timestamps = lambda i1, i2: LT(i1[1], i2[1])
        r = encode_permutation_check(self.interactions, encode_timestamps)
        return with_comment(r, f"EXECUTION BRIDGE axioms")
