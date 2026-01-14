from typing import Callable
from ..smt_utils import *

def encode_permutation_check(
    id: str,
    interactions: list[tuple[FNode, list[FNode]]],
    additional: Callable[[list[FNode], list[FNode]], FNode] = lambda _: TRUE()
) -> FNode:
    """
    Encodes a permutation check for the given list of interactions. It encodes
    a specialized property that puts the interactions in a total order where
    every odd-indexed interaction permutes with the subsequent even-indexed
    interaction: their data are equivalent and their multiplicities cancel out.
    Additionally, `additional` requirements can be encoded for even-indexed
    interactions and their subsequent odd-indexed interactions.
    The first and last interactions are "loose" in this encoding and we assume
    that an external chip takes care of those (as is the case for OpenVM).

    * Assumes that all interactions have the same number of arguments.
    * Auxiliary variables are named using the prefix `id`.
    """
    n = len(interactions)
    if n == 0:
        return TRUE()
    nargs = len(interactions[0][1])

    assert all(len(i[1]) == nargs for i in interactions)

    mults = [ Symbol(f'perm_{id}_{i}m', INT) for i in range(n) ]
    datas = [
        [ Symbol(f'perm_{id}_{i}d_{k}', INT) for k in range(nargs) ]
        for i in range(n)
    ]

    return And(
        # each set of datas vars is equal to one of the interactions
        *[
            Or(
                And(
                    Equals(mults[i], interactions[j][0]),
                    *[ Equals(datas[i][k], interactions[j][1][k]) for k in range(nargs) ],
                ) for j in range(n)
            ) for i in range(n)
        ],
        # correct permutation on odd->even pairs
        # correct additional on even->odd pairs
        *[
                additional(datas[i], datas[i+1])
            if i % 2 == 0 else
                And(
                    Equals(wrap_mod(Plus(mults[i], mults[i+1])), Int(0)),
                    *[Equals(datas[i][k], datas[i+1][k]) for k in range(nargs)],
                )
            for i in range(n-1)
        ],
    )