from .permutation_check import PermutationCheckMixin, TimestampCheckMixin
from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder, TimestampCheckMixin, PermutationCheckMixin):
    """
    Encodes execution bridge bus interactions. It implements a permutation
    check on all interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        super().__init__()

    def get_axioms(self) -> Optional[FNode]:
        ts = self.ordered_timestamp_check()
        r = self.ordered_permutation_check()
        return with_comment(
            And(ts, r),
            f"EXECUTION BRIDGE axioms"
        )

    def get_inputs(self) -> dict:
        return { 'execution bridge': self._interactions[0][1] }
    
    def get_outputs(self) -> dict:
        return { 'execution bridge': self._interactions[-1][1] }
