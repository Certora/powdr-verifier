from itertools import batched, pairwise
import itertools
from typing import Callable

from .single_interaction_encoder import BusInteraction
from ..smt.utils import *

def ordered_timestamp_check(
    interactions: list[BusInteraction],
    solver: Solver = None,
) -> Iterable[FNode]:
    def skip_to_next_non_zero(k: int) -> int:
        # skip over interactions that we know to have mult = 0
        while k < len(interactions) and solver.is_valid(Equals(interactions[k].mult, Int(0))):
            k += 1
            continue
        # and assert that the new one has mult != 0
        # this likely fails eventually, if the multiplicity can not be derived from the constraints
        assert solver.is_valid(Not(Equals(interactions[k].mult, Int(0))))
        return k

    if solver is None:
        logging.warning('ordered timestamp check: no solver provided, may be incorrect')
        return And(
            LT(b[0].args[-1], b[1].args[-1])
            for b in batched(interactions, 2) if len(b) == 2
        )

    res = []
    i = 0
    while i < len(interactions) - 1:
        i = skip_to_next_non_zero(i)
        j = skip_to_next_non_zero(i + 1)
        if j >= len(interactions):
            break
        res.append(LT(interactions[i].args[-1], interactions[j].args[-1]))
        i = j + 1
    
    return And(*res)
            

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
    def def_vars(id: int):
        return [ Symbol(f'{identifier}-{id}-mult', MultiArrayType(INT, keywidth, INT)) ] + [
            Symbol(f'{identifier}-{id}-data{k}', MultiArrayType(INT, keywidth, INT)) for k in range(datawidth) ]
    

    def update_multidim_array(
        input: FNode,
        keys: list[FNode]
    ) -> (FNode, FNode, FNode, list[FNode]):
        """
        Constructs the skeleton for an array update.
        - input: the old array of dimension len(keys)
        - keys: indices into the array
        returns:
        - oldval: the value of input at the given keys
        - newval: the new value at the given keys
        - store: the store operation resulting in a new array
        - conjuncts: the conjuncts to encode the update
        """
        conjuncts = []
        selects = [input]
        # stepwise select, add to selects and conjuncts as we go
        for id,key in enumerate(keys):
            newsym = Symbol(f'{input.symbol_name()}-{id+1}', selects[-1].get_type().elem_type)
            conjuncts.append(Equals(newsym, Select(selects[-1], key)))
            selects.append(newsym)
        
        # fresh variable for the new value
        newval = Symbol(f'{input.symbol_name()}-new', INT)
        # ensure selected and new value are in range
        conjuncts.append(field_symbol(selects[-1]))
        conjuncts.append(field_symbol(newval))

        # stepwise store, add to store as we go
        store = newval
        for id,key in enumerate(reversed(keys)):
            store = Store(selects[1 - id], key, store)
        
        return selects[-1], newval, store, conjuncts
    
    actual_inputs = def_vars(0)
    inputs = actual_inputs
    # accumulates everything needed to describe the permutation check
    conjuncts = []
    for id,i in enumerate(interactions):
        mult, keys, data = i
        assert len(keys) == keywidth
        assert len(data) == datawidth

        data = [mult, *data]

        # generate skeletons for array updates
        updates = [ update_multidim_array(input, keys) for input in inputs ]
        oldvals, newvals, stores, conj = zip(*updates)

        conjuncts.extend(itertools.chain(*conj))

        # encode the receive case
        conjuncts.append(
            with_comment(
                Implies( # receive: data[0] == -1
                    Equals(wrap_mod(Plus(data[0], Int(1))), Int(0)),
                    And(
                        # multiplicities
                        Equals(wrap_mod(oldvals[0]), Int(1)),
                        Equals(newvals[0], Int(0)),
                        # data + timestamps
                        *[ Equals(oldvals[k], data[k]) for k in range(1, len(newvals)) ],
                        *[ Equals(newvals[k], Int(0)) for k in range(1, len(newvals)) ]
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
                        Equals(oldvals[0], Int(0)),
                        Equals(newvals[0], Int(1)),
                        # data + timestamps
                        *[ Equals(oldvals[k], Int(0)) for k in range(1, len(newvals)) ],
                        *[ Equals(newvals[k], data[k]) for k in range(1, len(newvals)) ]
                    )
                ),
                f"send: mult == 1"
            )
        )

        news = def_vars(id+1)
        for k,s in enumerate(stores):
            conjuncts.append(Equals(news[k], s))
        inputs = news
    
    return conjuncts, actual_inputs, inputs
