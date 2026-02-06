from .permutation_check import PermutationCheckMixin, TimestampCheckMixin
from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder, TimestampCheckMixin, PermutationCheckMixin):
    """
    Encodes execution bridge bus interactions. It implements a permutation
    check on all interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        """Initialize an empty execution-bridge interaction list."""
        super().__init__()

    @attach_comment("EXECUTION BRIDGE axioms")
    def get_axioms(self) -> Optional[FNode]:
        """Return timestamp and permutation axioms over all execution-bridge interactions."""
        ts = self.ordered_timestamp_check()
        r = self.ordered_permutation_check()
        return And(ts, r)

    def get_inputs(self) -> dict:
        """Expose the first interaction's args as the bus input (if present)."""
        return { 'execution bridge': self._interactions[0][1] }
    
    def get_outputs(self) -> dict:
        """Expose the last interaction's args as the bus output (if present)."""
        return { 'execution bridge': self._interactions[-1][1] }
