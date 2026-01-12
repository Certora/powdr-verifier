from ..smt_utils import *

# encodes a formula that establishes a sequencing of the given interactions
# each interaction is a tuple of (data, timestamp) and a sequencing imposes a
# total order on the zero-indexed interactions.
# an interaction with even index is followed by an interaction such that the
# timestamp is greater.
# an interaction with odd index is followed by an interaction such that the
# data and the timestamp are the same.
def encode_sequencing(id: str, interactions: list[tuple[FNode, FNode]]) -> FNode:

    n = len(interactions)

    datas = [ Symbol(f'seq_{id}_{i}d', INT) for i in range(n) ]
    timestamps = [ Symbol(f'seq_{id}_{i}t', INT) for i in range(n) ]

    return And(
        # each data is equal to one of the interactions
        *[
            Or(
                And(
                    Equals(datas[i], interactions[j][0]),
                    Equals(timestamps[i], interactions[j][1])
                ) for j in range(n)
            ) for i in range(n)
        ],
        # sequencing on datas and timestamps
        *[
                GT(timestamps[i+1], timestamps[i])
            if i % 2 == 0 else
                And(Equals(datas[i], datas[i+1]), Equals(timestamps[i], timestamps[i+1]))
            for i in range(n-1)
        ],
    )
