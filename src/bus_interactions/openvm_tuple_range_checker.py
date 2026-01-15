from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class OpenVMTupleRangeCheckerEncoder(SingleInteractionEncoder):
    # taken from openvm/extensions/rv32im/circuit/src/extension/mod.rs:default_range_tuple_checker_sizes()
    # but openvm/extensions/bigint/circuit/src/extension/mod.rs has other values...
    MAX_0 = 1 << 8
    MAX_1 = 8 * (1 << 8)

    def encode(self, mult: Any, x: Any, y: Any) -> FNode:
        """
        Encodes tuple range checker bus interactions. It constrains the values
        of `x` and `y` to be in the range [0, MAX_0] and [0, MAX_1], respectively.
        `MAX_0` and `MAX_1` are constants from the VM config.
        """
        return And(
            LE(Int(0), x), LT(x, Int(self.MAX_0)),
            LE(Int(0), y), LT(y, Int(self.MAX_1)),
        )
