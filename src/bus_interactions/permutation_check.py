from itertools import batched, pairwise
import itertools

from ..smt.utils import *


class TimestampCheckMixin:
    """Mixin providing axioms that enforce monotonic timestamps over bus interactions."""

    @simple_profile
    def ordered_timestamp_check(self) -> FNode:
        """Constrain timestamps of consecutive interaction pairs to be strictly increasing."""
        res = []
        for batch in batched(self._interactions, 2):
            if len(batch) != 2:
                continue
            a, b = batch
            # for now we assume that zeroness of a.mult and b.mult are equivalent
            res.append(
                Implies(
                    Not(Equals(wrap_mod(a.mult), Int(0))), LT(a.args[-1], b.args[-1])
                )
            )

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
            for id, (a, b) in enumerate(pairwise(self._interactions)):
                if id % 2 == 1:
                    # correct permutation on odd->even pairs
                    yield And(
                        Equals(wrap_mod(Plus(a.mult, b.mult)), Int(0)),
                        *[Equals(a, b) for a, b in zip(a.args, b.args, strict=True)],
                    )

        return And(*encode())

    @simple_profile
    def array_permutation_check(
        self,
        keywidth: int,
        datawidth: int,
        interactions: list[tuple[FNode, list[FNode], list[FNode]]],
    ) -> (list[FNode], list[FNode], list[FNode], list[FNode]):
        if len(interactions) == 0:
            return [], [], [], [], []
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
            return [
                self._symbol(f"{self.NAME}-{id}-hadinput", MultiArrayType(INT, keywidth, BOOL)),
                self._symbol(f"{self.NAME}-{id}-mult", MultiArrayType(INT, keywidth, INT)),
            ] + [
                self._symbol(f"{self.NAME}-{id}-data{k}", MultiArrayType(INT, keywidth, INT))
                for k in range(datawidth)
            ]

        intermediates = set()

        def update_multidim_array(
            input: FNode, keys: list[FNode]
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
            for id, key in enumerate(keys):
                newsym = Symbol(
                    f"{input.symbol_name()}-{id + 1}", selects[-1].get_type().elem_type
                )
                conjuncts.append(Equals(newsym, Select(selects[-1], wrap_mod(key))))
                selects.append(newsym)
                intermediates.add(newsym)

            # fresh variable for the new value
            newval = Symbol(f"{input.symbol_name()}-new", newsym.get_type())
            intermediates.add(newval)

            # stepwise store, add to store as we go
            store = newval
            for id, key in enumerate(reversed(keys)):
                store = Store(selects[1 - id], wrap_mod(key), store)

            return (
                selects[-1],
                newval,
                store,
                conjuncts,
            )

        actual_inputs = def_vars(0)
        intermediates |= set(actual_inputs)
        inputs = actual_inputs
        # accumulates everything needed to describe the permutation check
        conjuncts = [Equals(actual_inputs[0], Array(INT, Array(INT, Bool(False))))]
        isinputs = [
            self._symbol(f"{self.NAME}-{id}-isinput", BOOL)
            for id in range(len(interactions))
        ]
        intermediates |= set(isinputs)
        for id, i in enumerate(interactions):
            mult, keys, data = i
            assert len(keys) == keywidth
            assert len(data) == datawidth

            data = [None, mult, *data]

            # generate skeletons for array updates
            updates = [update_multidim_array(input, keys) for input in inputs]
            oldvals, newvals, stores, conj = zip(*updates)

            bounds = []
            for oldval, newval in zip(oldvals, newvals):
                if oldval.get_type().is_int_type():
                    bounds.append(field_symbol(oldval))
                    bounds.append(field_symbol(newval))

            conjuncts.extend(itertools.chain(*conj))

            # encode hadinput
            conjuncts.append(
                with_comment(
                    And(
                        Implies(
                            Not(Equals(data[1], Int(0))),
                            And(
                                newvals[0],
                                Implies(Not(oldvals[0]), isinputs[id]),
                                Implies(oldvals[0], Not(isinputs[id])),
                            ),
                        ),
                        Implies(
                            Equals(data[1], Int(0)),
                            And(
                                Equals(newvals[0], oldvals[0]),
                                Not(isinputs[id]),
                            ),
                        ),
                    ),
                    "encode hadinput and isinput",
                )
            )

            # encode the receive case
            assert oldvals[1].is_symbol()
            conjuncts.append(
                with_comment(
                    Implies(  # receive: data[0] == -1
                        Equals(wrap_mod(Plus(data[1], Int(1))), Int(0)),
                        And(
                            # multiplicities
                            Equals(oldvals[1], Int(1)),
                            Equals(newvals[1], Int(0)),
                            # data + timestamps
                            *[
                                Equals(oldvals[k], wrap_mod(data[k]))
                                for k in range(2, len(newvals))
                            ],
                            *[
                                Equals(newvals[k], Int(0))
                                for k in range(2, len(newvals))
                            ],
                            # ensure intermediate values are in range
                            *bounds,
                        ),
                    ),
                    "receive: mult == -1",
                )
            )
            # encode the send case
            conjuncts.append(
                with_comment(
                    Implies(  # send: data[0] == 1
                        Equals(wrap_mod(Minus(data[1], Int(1))), Int(0)),
                        And(
                            # multiplicities
                            Equals(oldvals[1], Int(0)),
                            Equals(newvals[1], Int(1)),
                            # data + timestamps
                            *[
                                Equals(oldvals[k], Int(0))
                                for k in range(2, len(newvals))
                            ],
                            *[
                                Equals(newvals[k], wrap_mod(data[k]))
                                for k in range(2, len(newvals))
                            ],
                            # ensure intermediate values are in range
                            *bounds,
                        ),
                    ),
                    "send: mult == 1",
                )
            )
            # encode the zero case: everything is unchanged
            # do not bound intermediate values: this entire sequence may be disabled,
            # and then these bounds only lead to false positives
            conjuncts.append(
                with_comment(
                    Implies(  # send: data[0] == 0
                        Equals(wrap_mod(data[1]), Int(0)),
                        And(
                            *[
                                Equals(newvals[k], oldvals[k])
                                for k in range(1, len(newvals))
                            ]
                        ),
                    ),
                    "ignore: mult == 0",
                )
            )

            news = def_vars(id + 1)
            intermediates |= set(news)
            for k, s in enumerate(stores):
                conjuncts.append(Equals(news[k], s))
            inputs = news

        conjuncts = [c for c in conjuncts]
        outputs = actual_inputs[1:] # remove hadinput variables
        inputs = inputs[1:] # remove hadinput variables
        return conjuncts, outputs, intermediates, inputs, isinputs


    @simple_profile
    def busat_permutation_check(
        self,
        interactions: list,
        is_memory: bool = True
    ) -> FNode:
        """Encode pairwise matching with pseudo-boolean constraints for a group of interactions."""
        n = len(interactions)
        constraints: list[Any] = []

        inputs = []
        intermediates = []
        outputs = []
        isinputs = []

        # Create match variables for ordered pairs i < j
        local_match_vars: dict[tuple[int, int], Any] = {}
        self.match_vars: dict[tuple[int, int], Any] = {}
        for i in range(n):
            for j in range(i + 1, n):
                bi, bj = interactions[i], interactions[j]
                mv = self._symbol(f"{self.NAME}_{i}_{j}", BOOL)
                local_match_vars[(i, j)] = mv
                self.match_vars[(i, j)] = mv

                # m_i_j => (mul_i + mul_j == 0 && mul_i != 0 && mul_j != 0)
                constraints.append(
                    with_comment(
                        Implies(
                            mv,
                            And(
                                Equals(wrap_mod(Plus(bi.mult, bj.mult)), Int(0)),
                                Not(Equals(wrap_mod(bi.mult), Int(0))),
                                Not(Equals(wrap_mod(bj.mult), Int(0))),
                            )
                        ),
                        f"pairwise match ({i},{j}): {bi.mult} + {bj.mult} == 0"
                    )
                )

                # m_i_j => arg_k_i == arg_k_j for all args
                for arg_i, arg_j in zip(bi.args, bj.args):
                    constraints.append(
                        with_comment(
                            Implies(mv, Equals(wrap_mod(Minus(arg_i, arg_j)), Int(0))),
                            f"pairwise match ({i},{j}): {arg_i} == {arg_j}"
                        )
                    )

        # Self-match variables: interaction i balanced by itself
        # Also collect involved match vars per interaction for pseudo-boolean constraints
        involved: dict[int, list[z3.BoolRef]] = {i: [] for i in range(n)}
        for i in range(n):
            bi = interactions[i]
            mv = self._symbol(f"{self.NAME}_{i}_{i}", BOOL)
            self.match_vars[(i, i)] = mv
            involved[i].append(mv)

            # Self-match axiom: MEM allows mul in {-1, 0, 1}; BUS requires mul == 0
            is_mem = n > 0 and is_memory
            if is_mem:
                constraints.append(
                    with_comment(
                        Implies(mv,
                            Or(
                                Equals(wrap_mod(Plus(bi.mult, Int(1))), Int(0)),
                                Equals(wrap_mod(Plus(bi.mult, Int(0))), Int(0)),
                                Equals(wrap_mod(Plus(bi.mult, Int(-1))), Int(0)),
                            )
                        ),
                        f"self-match {i}: {bi.mult} == -1, 0, 1"
                    )
                )
            else:
                constraints.append(
                    with_comment(
                        Implies(mv, Equals(wrap_mod(bi.mult), Int(0))),
                        f"self-match {i}: {bi.mult} == 0"
                    )
                )

        for (i, j), mv in local_match_vars.items():
            involved[i].append(mv)
            involved[j].append(mv)

        # Per interaction: exactly one match (AtMost 1 + AtLeast 1)
        for i in range(n):
            constraints.append(
                with_comment(
                    AtMostOne(*involved[i]),
                    f"at most one match for {i}"
                )
            )
            constraints.append(
                with_comment(
                    Or(*involved[i]),
                    f"at least one match for {i}"
                )
            )
        
        if is_memory:
            ts_entry = self._symbol(f"{self.NAME}_TS_ENTRY", INT)

            # Collect self-match vars and field accessors per interaction
            n = len(interactions)
            sm_vars: list[FNode] = []
            muls: list[Any] = []
            timestamps: list[Any] = []
            addr_spaces: list[Any] = []
            pointers: list[Any] = []

            bytes_list: list[list[Any]] = []

            for i in range(n):
                mem = interactions[i]
                sm_vars.append(self.match_vars[(i, i)])
                muls.append(mem.mult)
                timestamps.append(mem.args[-1])
                addr_spaces.append(mem.args[0])
                pointers.append(mem.args[1])
                bytes_list.append(mem.args[2:-1])

            # Per-interaction: input self-match => ts < TS_ENTRY and bytes in [0, 255]
            for i in range(n):
                input_self = And(sm_vars[i], Equals(wrap_mod(Plus(muls[i], Int(1))), Int(0)))
                constraints.append(
                    with_comment(
                        Implies(input_self, LT(timestamps[i], ts_entry)),
                        f"self-match {i} small ts: {timestamps[i]} < {ts_entry}"
                    )
                )
                for b in bytes_list[i]:
                    constraints.append(
                        with_comment(
                            Implies(input_self, And(GE(b, Int(0)), LE(b, Int(255)))),
                            f"self-match {i} bytes: {b} in [0, 255]"
                        )
                    )

            # Pairwise constraints for distinct inputs and distinct outputs
            for i in range(n):
                inputs.append(
                    And(
                        sm_vars[i],
                        Equals(wrap_mod(Plus(muls[i], Int(1))), Int(0))
                    )
                )
                outputs.append(
                    And(
                        sm_vars[i],
                        Equals(wrap_mod(Minus(muls[i], Int(1))), Int(0))
                    )
                )
                for j in range(i + 1, n):
                    # Distinct inputs
                    both_input = And(
                        sm_vars[i],
                        Equals(wrap_mod(Plus(muls[i], Int(1))), Int(0)),
                        sm_vars[j],
                        Equals(wrap_mod(Plus(muls[j], Int(1))), Int(0)),
                    )
                    constraints.append(
                        with_comment(
                            Implies(both_input, Not(Equals(timestamps[i], timestamps[j]))),
                            f"inputs {i} and {j} distinct timestamps: {timestamps[i]} != {timestamps[j]}"
                        )
                    )
                    constraints.append(
                        with_comment(
                            Implies(
                                both_input,
                                Not(And(
                                    Equals(addr_spaces[i], addr_spaces[j]),
                                    Equals(pointers[i], pointers[j])
                                )),
                            ),
                            f"inputs {i} and {j} distinct address spaces and pointers: {addr_spaces[i]} != {addr_spaces[j]} or {pointers[i]} != {pointers[j]}"
                        )
                    )

                    # Distinct outputs
                    both_output = And(
                        sm_vars[i],
                        Equals(wrap_mod(Minus(muls[i], Int(1))), Int(0)),
                        sm_vars[j],
                        Equals(wrap_mod(Minus(muls[j], Int(1))), Int(0)),
                    )
                    constraints.append(
                        with_comment(
                            Implies(both_output, Not(Equals(timestamps[i], timestamps[j]))),
                            f"outputs {i} and {j} distinct timestamps: {timestamps[i]} != {timestamps[j]}"
                        )
                    )
                    constraints.append(
                        with_comment(
                            Implies(
                                both_output,
                                Not(And(
                                    Equals(addr_spaces[i], addr_spaces[j]),
                                    Equals(pointers[i], pointers[j])
                                ))
                            ),
                            f"outputs {i} and {j} distinct address spaces and pointers: {addr_spaces[i]} != {addr_spaces[j]} or {pointers[i]} != {pointers[j]}"
                        )
                    )

        return constraints, inputs, outputs, intermediates, isinputs
