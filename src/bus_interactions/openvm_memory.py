import itertools
import logging
from typing import Any

from .permutation_check import PermutationCheckMixin, TimestampCheckMixin

from .single_interaction_encoder import BusInteraction, SingleInteractionEncoder

from ..smt.utils import *


class MemoryAnalysis:
    """
    This class performs an alias analysis on a list of memory accesses,
    represented by their address space and pointer. The result is a list of
    equivalence classes where of such accesses that are equivalent.
    Additionally, each equivalence class contains a list of possibly equivalent
    accesses that can alias depending on the actual trace.

    The analysis proceeds in two stages:
    1. implied aliasing:
       Groups memory accesses whose equivalence is implied by the constraints.
    2. possible aliasing:
       For each equivalence class, find all other equivalence classes that can
       alias with it, but are not implied aliases.

    The result is a set of enhanced equivalence classes, each consisting of a
    set of accesses (that are implied aliases) and another set of accesses
    (that are possible but not implied aliases).
    """

    def __init__(self, constraints: list[FNode]):
        """Initialize alias-analysis state for the given global constraints."""
        self.implied_classes = {}
        self.possible_aliases = {}
        self.formula_selector = VarBaseFormulaSelector(constraints)

    def solve_implied_aliasing(self, accesses: list[tuple[FNode, FNode]]):
        """Compute alias equivalence classes that are implied by the constraints."""
        self.implied_classes = {(a[0], a[1]): (a[0], a[1]) for a in accesses}

        for a, b in itertools.combinations(self.implied_classes.values(), 2):
            if self.implied_classes[a] == self.implied_classes[b]:
                continue

            with Solver(
                logic=QF_UFNIA, incremental=True, solver_options={"timeout": 10000}
            ) as solver:
                for c in self.formula_selector.resolve_shallow_for([*a, *b]):
                    solver.add_assertion(c)

                same = And(Equals(a[0], b[0]), Equals(a[1], b[1]))
                logging.debug(f"checking if {same} is valid")
                if solver.is_valid(same):
                    self.implied_classes[b] = self.implied_classes[a]

    def solve_possible_aliasing(self):
        """For each implied class, find other classes that can alias in some model."""
        self.possible_aliases = {a: [] for a in self.implied_classes.values()}

        for a, b in itertools.combinations(self.possible_aliases.keys(), 2):
            with Solver(
                logic=UFNIA, incremental=True, solver_options={"timeout": 10000}
            ) as solver:
                for c in self.formula_selector.resolve_shallow_for([*a, *b]):
                    solver.add_assertion(c)

                same = And(Equals(a[0], b[0]), Equals(a[1], b[1]))
                logging.debug(f"checking if {same} is sat")
                if solver.is_sat(same):
                    self.possible_aliases[a].append(b)
                    self.possible_aliases[b].append(a)

    def get_equivalence_classes(
        self,
    ) -> frozenset[tuple[frozenset[FNode], frozenset[FNode]]]:
        """Return implied alias sets paired with their corresponding possible-alias sets."""
        return frozenset(
            [
                (
                    frozenset(
                        [
                            a
                            for a in self.implied_classes
                            if self.implied_classes[a] == representative
                        ]
                    ),
                    frozenset(self.possible_aliases[representative]),
                )
                for representative in set(self.implied_classes.values())
            ]
        )


class OpenVMMemoryEncoder(
    SingleInteractionEncoder, PermutationCheckMixin, TimestampCheckMixin
):
    """
    Encodes memory bus interactions. It implements a permutation check on all
    interactions and requires their timestamps increase.
    """

    NAME = "memory"

    def __init__(self) -> None:
        """Initialize encoder state for memory interactions (analysis computed in `pre_analysis`)."""
        super().__init__()
        self.interactions = {}
        self.name_or_id = NameOrIdGenerator()
        self.analysis = None

    def _sorted_interactions(self) -> list[tuple[FNode, Any]]:
        """Return interactions sorted by syntactic size of `(address_space, pointer)`."""
        return sorted(self._interactions, key=lambda i: i[1][0].size() + i[1][1].size())

    def pre_analysis(self) -> None:
        """Run alias analysis to compute implied and possible pointer aliasing classes."""
        if ARGS().skip_memory_analysis:
            logging.warning("skipping memory analysis")
            return

        accesses = sorted(
            [(i[1][0], i[1][1]) for i in self._interactions],
            key=lambda i: i[0].size() + i[1].size(),
        )
        self.analysis = MemoryAnalysis(self.constraints())
        self.analysis.solve_implied_aliasing(accesses)
        self.analysis.solve_possible_aliasing()

        logging.warning("results of memory analysis")
        for access, repr in self.analysis.implied_classes.items():
            if access != repr:
                logging.warning(f"\t{repr} == {access}")
        for access, possible in self.analysis.possible_aliases.items():
            if possible:
                logging.warning(f"\t{access} possibly aliases with")
                for p in possible:
                    if access != p:
                        logging.warning(f"\t\t{p}")

    def group_interactions(self):
        """Group interactions by implied alias class and replicate into possible-alias buckets."""
        if not self.analysis:
            logging.warning("no memory analysis performed, skipping memory bus")
            return {}
        res = {}

        for i in self._interactions:
            mult, (address_space, pointer, args, timestamp) = i
            interaction = (mult, args + [timestamp])
            access = (address_space, pointer)
            repr = self.analysis.implied_classes[access]
            if repr not in res:
                res[repr] = []
            res[repr].append((interaction, True))
            for alias in self.analysis.possible_aliases[repr]:
                if alias not in res:
                    res[alias] = []
                res[alias].append((interaction, False))

        return res

    def encode_pointwise(
        self,
        mult: FNode,
        address_space: FNode,
        pointer: FNode,
        data: list[FNode],
        timestamp: FNode,
    ) -> FNode:
        """(Currently a stub) Placeholder for per-interaction local memory constraints."""
        if address_space.is_int_constant() and address_space.constant_value() == 0:
            assert mult.is_int_constant() and mult.constant_value() == 0
        return None
        return with_comment(
            Implies(
                # Equals(wrap_mod(mult), wrap_mod(Int(-1))),
                TRUE(),
                And(*[And(LE(Int(0), d), LE(d, Int(255))) for d in data]),
            ),
            f"MEMORY interaction for {address_space} {pointer}",
        )

    def encode_all(self) -> Iterable[FNode]:
        """Return timestamp + array-based permutation axioms for the memory bus."""
        ts = self.ordered_timestamp_check()
        match ARGS().memory_encoding:
            case "array":
                permutation_axioms, inputs, intermediates, outputs, isinputs = (
                    self.array_permutation_check(
                        f"{self._cur_state.name}-mem",
                        keywidth=2,
                        datawidth=5,
                        interactions=[
                            (mult, [a, p], [*args, t])
                            for mult, (a, p, args, t) in self._interactions
                        ],
                    )
                )
            case "busat":
                permutation_axioms, inputs, intermediates, outputs, isinputs = (
                    self.busat_permutation_check(
                        f"{self._cur_state.name}-mem",
                        interactions=[
                            BusInteraction(mult, [a, p, *args, t])
                            for mult, (a, p, args, t) in self._interactions
                        ],
                        is_memory=True,
                    )
                )
            case _:
                raise ValueError(f"Invalid memory encoding: {ARGS().memory_encoding}")
        self.inputs = inputs
        self.auxiliaries = intermediates
        self.outputs = outputs
        assume_bytes = [
            with_comment(
                Implies(
                    isinput,
                    And(
                        *[
                            And(LE(Int(0), d), LE(d, Int(255)))
                            for d in self._interactions[id].args[2]
                        ]
                    ),
                ),
                f"assume bytes if #{id} is input",
            )
            for id, isinput in enumerate(isinputs)
        ]
        #yield with_comment(ts, f"{self.NAME} timestamp check")
        yield with_comment(And(*permutation_axioms), f"{self.NAME} permutation axioms")
        yield with_comment(And(*assume_bytes), f"{self.NAME} assume bytes")
