from itertools import pairwise
from typing import Callable
from ..smt.utils import *

def ordered_permutation_check(
    interactions: list[tuple[tuple[FNode, list[FNode]], bool]],
    additional: Callable[[list[FNode], list[FNode]], FNode] = lambda _: TRUE()
) -> FNode:
    """
    Encodes a permutation check for the given list of interactions.
    Every odd-indexed interaction permutes with the subsequent even-indexed
    interaction: their data are equivalent and their multiplicities cancel out.
    Additionally, `additional` requirements can be encoded for even-indexed
    interactions and their subsequent odd-indexed interactions.
    The first and last interactions are "loose" in this encoding and we assume
    that an external chip takes care of those (as is the case for OpenVM).

    * Assumes that the interactions are already well-ordered.
    * Assumes that all interactions have the same number of arguments.
    * Auxiliary variables are named using the prefix `id`.
    """
    n = len(interactions)
    if n == 0:
        return TRUE()

    def encode():
        for id,(((m1,d1),impl1),((m2,d2),impl2)) in enumerate(pairwise(interactions)):
            # TODO: Handle implied flags (impl1, impl2)
            #assert impl1 and impl2, f"encoding for possible permutation not yet supported"
            if not impl1 or not impl2:
                logging.warning(f"encoding for possible permutation not yet supported")
                logging.warning(f"access 1: {d1}")
                logging.warning(f"access 2: {d2}")
            if id % 2 == 0:
                # correct additional on even->odd pairs
                yield additional(d1, d2)
            else:
                # correct permutation on odd->even pairs
                yield And(
                    Equals(wrap_mod(Plus(m1, m2)), Int(0)),
                    *[ Equals(a, b) for a,b in zip(d1, d2, strict=True) ],
                )

    return And(*encode())

def array_permutation_check(
    identifier: str,
    width: int,
    interactions: list[tuple[FNode, list[FNode]]],
) -> list[FNode]:
    """
    Encodes a permutation check for the given list of interactions.
    """

    input = Symbol(f'{identifier}-0', MultiArrayType(INT, width, INT))
    conjuncts = []
    for id,i in enumerate(interactions):
        mult, data = i
        assert len(data) == width
        cur = [input] + [
            Symbol(f'{identifier}-{id}k{k}', MultiArrayType(INT, width - k, INT))
            for k in range(1, width + 1)
        ]
        for k in range(width):
            conjuncts.append(Equals(cur[k+1], Select(cur[k], data[k])))
        
        store = cur[-1] + mult
        for k in range(width-1,-1,-1):
            store = Store(cur[k], data[k], store)
        
        new = Symbol(f'{identifier}-{id+1}', MultiArrayType(INT, width, INT))
        conjuncts.append(Equals(new, store))
        input = new
    
    return conjuncts
