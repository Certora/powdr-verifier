from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMTupleRangeCheckerEncoder(SingleInteractionEncoder):
    def encode(self) -> FNode:
        return True()
