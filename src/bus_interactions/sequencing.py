from pysmt.fnode import FNode
from pysmt.shortcuts import *
from pysmt.typing import *

# encodes a formula that establishes a sequencing of the given interactions
# each interaction is a tuple of (data, timestamp) and a sequencing imposes a
# total order on the zero-indexed interactions.
# an interaction with even index is followed by an interaction such that the
# data is the same and the timestamp is greater.
# an interaction with odd index is followed by an interaction such that the
# data is different and the timestamp is the same.
def encode_sequencing(id: str, interactions: list[tuple[FNode, FNode]]) -> FNode:

    n = len(interactions)

    datas = [ Symbol(f'seqd_{id}_{i}', INT) for i in range(n) ]
    timestamps = [ Symbol(f'seqt_{id}_{i}', INT) for i in range(n) ]

    return And(
        # each data is equal to one of the interactions
        *[ Or(Equals(datas[i], interactions[j][0]) for j in range(n)) for i in range(n)],
        # each timestamp is equal to one of the interactions
        *[ Or(Equals(timestamps[i], interactions[j][1]) for j in range(n)) for i in range(n)],
        # sequencing on datas and timestamps
        *[
                And(Equals(datas[i], datas[i+1]), GT(timestamps[i+1], timestamps[i]))
            if i % 2 == 0 else
                And(NotEquals(datas[i], datas[i+1]), Equals(timestamps[i], timestamps[i+1]))
            for i in range(n-1)
        ],
    )
