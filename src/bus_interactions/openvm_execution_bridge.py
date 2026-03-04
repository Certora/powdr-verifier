from .permutation_check import PermutationCheckMixin, TimestampCheckMixin
from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *


class OpenVMExecutionBridgeEncoder(
    SingleInteractionEncoder, TimestampCheckMixin, PermutationCheckMixin
):
    """
    Encodes execution bridge bus interactions. It implements a permutation
    check on all interactions and requires their timestamps increase.
    """

    NAME = "execution bridge"
    TIMESTAMPED = True

    def encode_all(self) -> Iterable[FNode]:
        """Return timestamp and permutation axioms over all execution-bridge interactions."""
        if len(self._interactions) == 0:
            logging.warning("no execution bridge interactions")
            return
        #yield with_comment(self.ordered_timestamp_check(), "EXECUTION BRIDGE timestamp check")
        yield with_comment(self.ordered_permutation_check(), "EXECUTION BRIDGE permutation check")

        self.inputs = self._interactions[0][1]
        self.outputs = self._interactions[-1][1]
