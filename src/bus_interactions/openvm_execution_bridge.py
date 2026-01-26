from .permutation_check import ordered_permutation_check, ordered_timestamp_check
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
        ts = ordered_timestamp_check([i[1][1] for i in self._interactions])
        r = ordered_permutation_check([(i, True) for i in self._interactions])
        return with_comment(
            And(ts, r),
            f"EXECUTION BRIDGE axioms"
        )
