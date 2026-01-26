from .permutation_check import ordered_permutation_check
from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder):
    """
    Encodes execution bridge bus interactions. It implements a permutation
    check on all interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        super().__init__()

    def get_axioms(self) -> list[FNode]:
        encode_timestamps = lambda i1, i2: LT(i1[1], i2[1])
        r = ordered_permutation_check(
            [(i, True) for i in self._interactions],
            encode_timestamps
        )
        return with_comment(r, f"EXECUTION BRIDGE axioms")
