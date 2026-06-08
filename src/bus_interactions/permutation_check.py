"""Mixins and formulas for multiset permutation invariants and timestamp monotonicity."""
from itertools import batched, pairwise
import itertools

from ..smt.utils import *


def keyed_io_relation(
    name: str,
    interactions_a: list,
    interactions_b: list,
    is_a: list[FNode],
    is_b: list[FNode],
) -> FNode:
    """Relate two sets of memory-bus I/O across independent encodings.

    Used in completeness/soundness checks to require that the *before* and
    *after* APC dumps expose the same inputs (or outputs), without fixing which
    interaction index carries which record. Internal permutation/balancing on each
    side is handled separately by ``plain_permutation_check``.

    Each interaction is a ``BusInteraction`` whose ``args`` are
    ``[address_space, pointer, *data, timestamp]``. The *key*
    ``(address_space, pointer)`` identifies a memory cell; ``data`` and
    ``timestamp`` are the payload. The encoding assumes that among interactions
    marked as I/O on one side, keys are pairwise distinct (enforced by the plain
    permutation axioms).

    Arguments:
        name: Comment prefix for generated conjuncts (e.g. ``"INPUT RELATION"``).
        interactions_a: Interactions from the left/before encoder, same order as
            when that side's permutation check was built.
        interactions_b: Interactions from the right/after encoder.
        is_a: For each index ``i`` into ``interactions_a``, a boolean formula that
            is true exactly when that interaction counts as the chosen I/O kind
            (input or output) on side A.
        is_b: Same for side B, aligned with ``interactions_b``.

    Returns a conjunction of three constraint families (see inline comments below).
    """
    n, m = len(interactions_a), len(interactions_b)
    parts: list[FNode] = []

    def key_eq(i: int, j: int) -> FNode:
        """``(address_space, pointer)`` agree at indices ``i`` (A) and ``j`` (B)."""
        return And(
            field_eq(interactions_a[i].args[0], interactions_b[j].args[0]),
            field_eq(interactions_a[i].args[1], interactions_b[j].args[1]),
        )

    def full_eq(i: int, j: int) -> FNode:
        """All args (key, data, timestamp) agree at indices ``i`` and ``j``."""
        return And(
            *[
                field_eq(a, b)
                for a, b in zip(interactions_a[i].args, interactions_b[j].args, strict=True)
            ]
        )

    # Same key and both marked I/O => identical record (bytes, timestamp, keys).
    for i in range(n):
        for j in range(m):
            parts.append(
                with_comment(
                    Implies(And(is_a[i], is_b[j], key_eq(i, j)), full_eq(i, j)),
                    f"{name}: key match => full eq ({i},{j})",
                )
            )

    # Every I/O record on A has some I/O record on B at the same key.
    for i in range(n):
        parts.append(
            with_comment(
                Implies(
                    is_a[i],
                    Or([And(is_b[j], key_eq(i, j)) for j in range(m)]) if m else FALSE(),
                ),
                f"{name}: left record {i} has counterpart",
            )
        )

    # Every I/O record on B has some I/O record on A at the same key.
    for j in range(m):
        parts.append(
            with_comment(
                Implies(
                    is_b[j],
                    Or([And(is_a[i], key_eq(i, j)) for i in range(n)]) if n else FALSE(),
                ),
                f"{name}: right record {j} has counterpart",
            )
        )

    return And(*parts) if parts else TRUE()


def boolean_propagate(conjuncts: list[FNode]) -> list[FNode]:
    literals: list[FNode] = []
    remaining = [keep_comment(f.simplify(), f) for f in conjuncts]
    substitutions: dict[FNode, FNode] = {}

    def record_literal(lit: FNode) -> bool:
        if lit.is_symbol(BOOL):
            sym, val = lit, TRUE()
        elif lit.is_not() and lit.arg(0).is_symbol(BOOL):
            sym, val = lit.arg(0), FALSE()
        else:
            return False
        if sym in substitutions:
            return False
        substitutions[sym] = val
        literals.append(lit)
        return True

    while True:
        new_binding = False
        next_remaining: list[FNode] = []
        for f in remaining:
            f = keep_comment(f.simplify(), f)
            if record_literal(f):
                new_binding = True
            elif not f.is_true():
                next_remaining.append(f)
        remaining = (
            [keep_comment(g.substitute(substitutions), g) for g in next_remaining]
            if substitutions
            else next_remaining
        )
        if not new_binding:
            break

    return literals + remaining


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
                    Not(Equals(wrap_mod(a.mult), Int(0))), field_lt(a.args[-1], b.args[-1])
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
                        *[Equals(wrap_mod(Minus(a, b)), Int(0)) for a, b in zip(a.args, b.args, strict=True)],
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

        USE_ITE_ENCODING = True

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

            for c in itertools.chain(*conj):
                conjuncts.append(c)

            if USE_ITE_ENCODING:

                mul_zero = Equals(wrap_mod(data[1]), Int(0))
                mul_pone = Equals(wrap_mod(Minus(data[1], Int(1))), Int(0))
                mul_mone = Equals(wrap_mod(Plus(data[1], Int(1))), Int(0))

                # encode hadinput
                conjuncts.append(
                    with_comment(
                        Equals(
                            newvals[0],
                            Ite(mul_zero, oldvals[0], TRUE())
                        ),
                        "new value for hadinput"
                    )
                )
                conjuncts.append(
                    with_comment(
                        Iff(
                            isinputs[id],
                            Ite(mul_zero, FALSE(), Not(oldvals[0]))
                        ),
                        "isinput logic",
                    )
                )
                # encode mult change logic
                conjuncts.append(
                    with_comment(
                        Or(mul_zero, mul_pone, mul_mone),
                        "sanity check on mult value"
                    )
                )
                conjuncts.append(
                    with_comment(
                        Equals(
                            oldvals[1],
                            Ite(
                                mul_mone,
                                Int(1),
                                Ite(mul_pone, Int(0), newvals[1])
                            )
                        ),
                        "value of old mult"
                    )
                )
                conjuncts.append(
                    with_comment(
                        Equals(
                            newvals[1],
                            Ite(
                                mul_mone,
                                Int(0),
                                Ite(mul_pone, Int(1), oldvals[1])
                            )
                        ),
                        "value of new mult"
                    )
                )
                conjuncts.append(
                    with_comment(
                        And(*[
                            Equals(
                                oldvals[k],
                                Ite(
                                    mul_mone,
                                    wrap_mod(data[k]),
                                    Ite(mul_pone, Int(0), oldvals[k])
                                )
                            )
                            for k in range(2, len(newvals))
                        ]),
                        "value of old data and timestamps"
                    )
                )
                conjuncts.append(
                    with_comment(
                        And(*[
                            Equals(
                                newvals[k],
                                Ite(
                                    mul_mone,
                                    Int(0),
                                    Ite(mul_pone, wrap_mod(data[k]), oldvals[k])
                                )
                            )
                            for k in range(2, len(newvals))
                        ]),
                        "value of new data and timestamps"
                    )
                )
            
            else:
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
                        Implies(  # receive: data[1] == -1
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
                            ),
                        ),
                        "receive: mult == -1",
                    )
                )
                # encode the send case
                conjuncts.append(
                    with_comment(
                        Implies(  # send: data[1] == 1
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
                        Implies(  # send: data[1] == 0
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
            mul_zero_store = Equals(wrap_mod(data[1]), Int(0))
            for k, s in enumerate(stores):
                conjuncts.append(
                    Equals(news[k], Ite(mul_zero_store, inputs[k], s))
                )
            inputs = news

        conjuncts = [c for c in conjuncts]
        outputs = actual_inputs[1:] # remove hadinput variables
        inputs = inputs[1:] # remove hadinput variables
        return conjuncts, outputs, intermediates, inputs, isinputs
    
    @simple_profile
    def plain_permutation_check(
        self,
        interactions: list,
        is_memory: bool = True
    ) -> tuple[list[FNode], list[FNode], list[FNode]]:
        """Encodes a permutation check in the spirit of busat."""
        conjuncts = []
        n = len(interactions)
        if n == 0:
            return [], [], []
        # provide match variables for all pairs i <= j
        is_inputs: dict[int, Any] = {
            i: self._symbol(f"{self.NAME}_isinput_{i}", BOOL)
            for i in range(n)
        }
        is_outputs: dict[int, Any] = {
            i: self._symbol(f"{self.NAME}_isoutput_{i}", BOOL)
            for i in range(n)
        }
        is_disableds: dict[int, Any] = {
            i: self._symbol(f"{self.NAME}_isdisabled_{i}", BOOL)
            for i in range(n)
        }
        match_vars: dict[tuple[int, int], Any] = {
            (i, j): self._symbol(f"{self.NAME}_match_{i}_{j}", BOOL)
            for i in range(n)
            for j in range(i, n)
        }

        def m(i: int, j: int) -> FNode:
            if i > j:
                return m(j, i)
            return match_vars[(i, j)]

        def mult(i: int) -> FNode:
            return interactions[i].mult

        def args(i: int) -> list[FNode]:
            return interactions[i].args

        def is_input(i: int) -> FNode:
            return is_inputs[i]
        def is_output(i: int) -> FNode:
            return is_outputs[i]
        def is_disabled(i: int) -> FNode:
            return is_disableds[i]

        def bus_arg_constants_distinct(ii: int, jj: int, key: int) -> bool:
            a, b = args(ii)[key], args(jj)[key]
            return a.is_int_constant() and not b.is_int_constant(a.constant_value())

        # multiplicity range constraints
        for i in range(n):
            conjuncts.append(
                with_comment(
                    Or(
                        field_eq(mult(i), Int(-1)),
                        field_eq(mult(i), Int(0)),
                        field_eq(mult(i), Int(1)),
                    ),
                    f"multiplicity {i} in {-1, 0, 1}"
                )
            )

        # a bunch of facts about self-matches
        for i in range(n):
            conjuncts.append(
                with_comment(
                    Iff(
                        m(i, i),
                        Or(
                            is_disabled(i),
                            is_input(i),
                            is_output(i),
                        )
                    ),
                    f"self-match {i}: disabled, input, or output"
                )
            )
            conjuncts.append(
                with_comment(
                    Iff(
                        is_disabled(i),
                        And(m(i, i), field_eq(mult(i)))
                    ),
                    f"disabled {i}: self-match and mult == 0"
                )
            )
            conjuncts.append(
                with_comment(
                    Iff(
                        is_input(i),
                        And(m(i, i), field_eq(mult(i), Int(-1)))
                    ),
                    f"input {i}: self-match and mult == -1"
                )
            )
            conjuncts.append(
                with_comment(
                    Iff(
                        is_output(i),
                        And(m(i, i), field_eq(mult(i), Int(1)))
                    ),
                    f"output {i}: self-match and mult == 1"
                )
            )
            # self-match: not m_i_i => not disabled, input or output, mult != 0
            conjuncts.append(
                with_comment(
                    Implies(
                        Not(m(i, i)),
                        And(
                            Not(is_disabled(i)),
                            Not(is_input(i)),
                            Not(is_output(i)),
                            Not(field_eq(mult(i))),
                        )
                    ),
                    f"no self-match {i}: neither disabled, input, nor output, mult != 0"
                )
            )

        for i in range(n):
            for j in range(i + 1, n):
                # pairwise match: mul_i + mul_j == 0 and mul_i != 0 and mul_j != 0
                conjuncts.append(
                    with_comment(
                        Implies(
                            m(i, j),
                            And(
                                Equals(wrap_mod(Plus(mult(i), mult(j))), Int(0)),
                                Not(Equals(wrap_mod(mult(i)), Int(0))),
                                Not(Equals(wrap_mod(mult(j)), Int(0)))
                            )
                        ),
                        f"match {i} and {j}: {mult(i)} + {mult(j)} == 0"
                    )
                )
                #if i == 1 and j == 4:
                #    continue
                # pairwise match: data_i == data_j
                conjuncts.append(
                    with_comment(
                        Implies(
                            m(i, j),
                            And(
                                Equals(wrap_mod(Minus(*z)), Int(0)) for z in zip(args(i), args(j), strict=True)
                            )
                        ),
                        f"match {i} and {j}: equal data"
                    )
                )

        # every interaction has exactly one match
        for i in range(n):
            conjuncts.append(
                with_comment(
                    ExactlyOne(*[m(i, j) for j in range(n)]),
                    f"interaction {i} has exactly one match"
                )
            )

        # no two inputs or two outputs have the same address space and pointer
        for i in range(n):
            for j in range(i + 1, n):
                conjuncts.append(
                    with_comment(
                        Implies(
                            Or(
                                And(is_input(i), is_input(j)),
                                And(is_output(i), is_output(j)),
                            ),
                            Or(
                                Not(Equals(args(i)[0], args(j)[0])),
                                Not(Equals(args(i)[1], args(j)[1])),
                            )
                        ),
                        f"inputs or outputs {i} and {j} have different address spaces or pointers"
                    )
                )
        
        # from hereon, the conjuncts are tuned to the actual inputs and might break on weird inputs
        # at least, they encode properties that are not immediately obvious from the specs

        for i in range(n):
            non_distinct = [
                t
                for t in range(i + 1, n)
                if not (bus_arg_constants_distinct(i, t, 0) or bus_arg_constants_distinct(i, t, 1))
            ]
            for jj, j in enumerate(non_distinct):
                for k in non_distinct[jj + 1 :]:
                    conjuncts.append(
                        with_comment(
                            Implies(
                                And(
                                    m(i, k),
                                    Equals(args(i)[0], args(j)[0]),
                                    Equals(args(i)[1], args(j)[1]),
                                ),
                                field_eq(mult(j)),
                            ),
                            f"match {i} and {k}: index {j} between with same key => mult==0",
                        )
                    )

        # inputs and outputs have each distinct timestamps
        for i in range(n):
            for j in range(i + 1, n):
                conjuncts.append(
                    with_comment(
                        Implies(
                            Or(
                                And(is_input(i), is_input(j)),
                                And(is_output(i), is_output(j)),
                            ),
                            Not(Equals(args(i)[-1], args(j)[-1])),
                        ),
                        f"inputs or outputs {i} and {j} have different timestamps"
                    )
                )
        
        # usually the first is an input and the last is an output. we have the
        # special zero-is-model check, though, and so we have to be a bit more
        # careful.
        conjuncts.append(
            with_comment(
                Implies(Not(field_eq(mult(0))), is_input(0)),
                f"first is an input"
            )
        )
        conjuncts.append(
            with_comment(
                Implies(Not(field_eq(mult(n - 1))), is_output(n - 1)),
                f"last is an output"
            )
        )

        return (
            boolean_propagate(conjuncts),
            [is_inputs[i] for i in range(n)],
            [is_outputs[i] for i in range(n)],
        )

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
