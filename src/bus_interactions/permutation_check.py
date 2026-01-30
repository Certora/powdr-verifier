from itertools import batched, pairwise
from typing import Callable

from .single_interaction_encoder import BusInteraction
from ..smt.utils import *

def ordered_timestamp_check(
    interaction_timestamps: list[BusInteraction],
) -> Iterable[FNode]:
    # TODO: handle mult = 0 case. It may not actually happen in practice, but we should handle it anyway.
    return And(
        LT(b[0].args[-1], b[1].args[-1])
        for b in batched(interaction_timestamps, 2) if len(b) == 2
    )

def ordered_permutation_check(
    interactions: list[tuple[tuple[FNode, list[FNode]], bool]]
) -> FNode:
    """
    Encodes a permutation check for the given list of interactions. We assume
    that the interactions are already well-ordered: two consecutive interactions
    where the first is even-indexed permute (their data is equivalent and their
    multiplicities cancel out).
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
            if id % 2 == 1:
                # correct permutation on odd->even pairs
                yield And(
                    Equals(wrap_mod(Plus(m1, m2)), Int(0)),
                    *[ Equals(a, b) for a,b in zip(d1, d2, strict=True) ],
                )

    return And(*encode())

def array_permutation_check(
    identifier: str,
    keywidth: int,
    datawidth: int,
    interactions: list[tuple[FNode, list[FNode], list[FNode]]],
) -> (list[FNode],list[FNode],list[FNode]):
    """
    Encodes a permutation check for the given list of interactions using an
    array encoding. This encoding is pretty specific to the memory bus, so we
    explain it using the memory bus as an example.
    We encode the state of the bus as arrays indexed by the address space and
    pointer, one array for the multiplicity and each data (including the
    timestamps).
    
    For each interaction, we update the arrays as follows where we have the
    "old" multiplicity and data (read/selected from the array), the "current"
    multiplicity and data (from the current interaction), and the "new"
    multiplicity and data (written/stored to the array).
    - if current mult == -1 (receive):
      - require that the interaction permutes with the current bus state:
        - require that the old multiplicity is one
        - require that the old data is equal to the current data
      - empty the bus:
        - set the new multiplicity to zero
        - set the new data to zero
    - if mult == 1 (send):
      - require that the bus is empty:
        - require that the previous multiplicity is zero
        - require that the old data is zero
      - send the interaction to the bus:
        - set the new multiplicity to one
        - set the new data to the current data

    Given that the array theory does not support n-ary selects and stores, the
    array updates are a bit convoluted.

    We return the encoding itself (list of conjuncts) as well as the inputs and outputs.
    """
    def def_vars(id: int, deg = keywidth):
        return [ Symbol(f'{identifier}-{id}-mult-{deg}', MultiArrayType(INT, deg, INT)) ] + [
            Symbol(f'{identifier}-{id}-data{k}-{deg}', MultiArrayType(INT, deg, INT)) for k in range(datawidth) ]
    
    actual_inputs = def_vars(0)
    inputs = actual_inputs
    # accumulates everything needed to describe the permutation check
    conjuncts = []
    for id,i in enumerate(interactions):
        mult, keys, data = i
        assert len(keys) == keywidth
        assert len(data) == datawidth

        data = [mult, *data]

        # here we accumulate the stepwise selections from the nested arrays
        # the first entry is the full array, then the selected array of
        # dimension n-1 etc until the last entry is the selected value.
        newcurs = [[i] for i in inputs]

        # stepwise select, add to newcurs and conjuncts as we go
        for deg in range(keywidth-1, -1, -1):        
            newcur = def_vars(id, deg=deg)
            for k,nc in enumerate(newcurs):
                conjuncts.append(Equals(newcur[k], Select(nc[-1], keys[keywidth - deg - 1])))
                newcurs[k].append(newcur[k])
        
        # ensure that the selected values are in range, just for sanity
        conjuncts.extend([field_symbol(s[-1]) for s in newcurs])
        
        # fresh variables to simplify the updates
        stores = [
            Symbol(f'{identifier}-{id}-mult-new', INT),
            *[
                Symbol(f'{identifier}-{id}-data{k}-new', INT)
                for k in range(datawidth)
            ]
        ]
        conjuncts.extend([field_symbol(s) for s in stores])

        # encode the receive case
        conjuncts.append(
            with_comment(
                Implies( # receive: data[0] == -1
                    Equals(wrap_mod(Plus(data[0], Int(1))), Int(0)),
                    And(
                        # multiplicities
                        Equals(wrap_mod(newcurs[0][-1]), Int(1)),
                        Equals(stores[0], Int(0)),
                        # data + timestamps
                        *[ Equals(newcurs[k+1][-1], data[k+1]) for k in range(len(stores)-1) ],
                        *[ Equals(stores[k+1], Int(0)) for k in range(len(stores)-1) ]
                    )
                ),
                f"receive: mult == -1"
            )
        )
        # encode the send case
        conjuncts.append(
            with_comment(
                Implies( # send: data[0] == 1
                    Equals(wrap_mod(Minus(data[0], Int(1))), Int(0)),
                    And(
                        # multiplicities
                        Equals(newcurs[0][-1], Int(0)),
                        Equals(stores[0], Int(1)),
                        # data + timestamps
                        *[ Equals(newcurs[k+1][-1], Int(0)) for k in range(len(stores)-1) ],
                        *[ Equals(stores[k+1], data[k+1]) for k in range(len(stores)-1) ]
                    )
                ),
                f"send: mult == 1"
            )
        )
        
        # now stepwise construct the stores. No need to keep the intermediates,
        # just overwrite the stores as we go.
        for deg in range(keywidth-1, -1, -1):
            for k,nc in enumerate(newcurs):
                stores[k] = Store(nc[deg], keys[deg], stores[k])
        
        # finally introduce fresh variables for the updated arrays.
        news = def_vars(id+1)
        for k,s in enumerate(stores):
            conjuncts.append(Equals(news[k], s))
        inputs = news
    
    return conjuncts, actual_inputs, inputs
