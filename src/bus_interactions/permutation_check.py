from itertools import batched, pairwise
import itertools

from ..rewriter import rewrite

from ..smt.utils import *

class TimestampCheckMixin:
    """Mixin providing axioms that enforce monotonic timestamps over bus interactions."""
    @simple_profile
    def ordered_timestamp_check(self) -> FNode:
        """Constrain timestamps of consecutive interaction pairs to be strictly increasing."""
        # sanity check: interactions with mult = 0 should not exist
        if self.solver() is not None:
            assert all(self.solver().is_sat(Not(Equals(i.mult, Int(0)))) for i in self._interactions)
            
        res = []
        for batch in batched(self._interactions, 2):
            if len(batch) != 2:
                continue
            a,b = batch
            # for now we assume that zeroness of a.mult and b.mult are equivalent
            assert self.solver().is_valid(Iff(Equals(a.mult, Int(0)), Equals(b.mult, Int(0))))
            res.append(Implies(Not(Equals(wrap_mod(a.mult), Int(0))), LT(a.args[-1], b.args[-1])))

        return And(*res)
            

class PermutationCheckMixin:
    """Mixin providing permutation-check encodings (pairwise and array-based) for bus interactions."""
    @simple_profile
    def ordered_permutation_check(self) -> FNode:
        """
        Encodes a permutation check for the given list of interactions. We assume
        that the interactions are already well-ordered: two consecutive interactions
        where the first is even-indexed permute (their data is equivalent and their
        multiplicities cancel out).
        """
        if len(self._interactions) == 0:
            return TRUE()

        def encode():
            """Yield conjuncts enforcing that odd/even interaction pairs permute and cancel."""
            for id,(a,b) in enumerate(pairwise(self._interactions)):
                if id % 2 == 1:
                    # correct permutation on odd->even pairs
                    yield And(
                        Equals(wrap_mod(Plus(a.mult, b.mult)), Int(0)),
                        *[ Equals(a, b) for a,b in zip(a.args, b.args, strict=True) ],
                    )

        return And(*encode())

    @simple_profile
    def array_permutation_check(
        self,
        identifier: str,
        keywidth: int,
        datawidth: int,
        interactions: list[tuple[FNode, list[FNode], list[FNode]]],
    ) -> (list[FNode],list[FNode],list[FNode],list[FNode]):
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
            """Create the per-step array symbols (mult + data arrays) for step `id`."""
            return [ Symbol(f'{identifier}-{id}-mult', MultiArrayType(INT, keywidth, INT)) ] + [
                Symbol(f'{identifier}-{id}-data{k}', MultiArrayType(INT, keywidth, INT)) for k in range(datawidth) ]
        
        intermediates = set()

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
                intermediates.add(newsym)
            
            # fresh variable for the new value
            newval = Symbol(f'{input.symbol_name()}-new', INT)
            # ensure selected and new value are in range
            conjuncts.append(field_symbol(selects[-1]))
            conjuncts.append(field_symbol(newval))
            intermediates.add(newval)

            # stepwise store, add to store as we go
            store = newval
            for id,key in enumerate(reversed(keys)):
                store = Store(selects[1 - id], key, store)
            
            return selects[-1], newval, store, conjuncts,
        
        actual_inputs = def_vars(0)
        intermediates |= set(actual_inputs)
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
            assert oldvals[0].is_symbol()
            conjuncts.append(
                with_comment(
                    Implies( # receive: data[0] == -1
                        Equals(wrap_mod(Plus(data[0], Int(1))), Int(0)),
                        And(
                            # multiplicities
                            Equals(oldvals[0], Int(1)),
                            Equals(newvals[0], Int(0)),
                            # data + timestamps
                            *[ Equals(oldvals[k], data[k]) for k in range(1, len(newvals)) ],
                            *[ Equals(newvals[k], Int(0)) for k in range(1, len(newvals)) ]
                        )
                    ),
                    "receive: mult == -1"
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
                    "send: mult == 1"
                )
            )

            news = def_vars(id+1)
            intermediates |= set(news)
            for k,s in enumerate(stores):
                conjuncts.append(Equals(news[k], s))
            inputs = news
        
        conjuncts = [ rewrite(c) for c in conjuncts ]
        return conjuncts, actual_inputs, intermediates, inputs
