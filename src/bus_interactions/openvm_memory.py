import itertools
import logging
from typing import Any

from .permutation_check import encode_permutation_check

from .single_interaction_encoder import SingleInteractionEncoder

from ..utils.smt_utils import *

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
        self.implied_classes = {}
        self.possible_aliases = {}
        self.formula_selector = VarBaseFormulaSelector(constraints)
    
    def solve_implied_aliasing(self, accesses: list[tuple[FNode, FNode]]):
        self.implied_classes = { (a[0], a[1]): (a[0], a[1]) for a in accesses }

        for a,b in itertools.combinations(self.implied_classes.values(), 2):
            if self.implied_classes[a] == self.implied_classes[b]:
                continue

            solver = Solver(logic=QF_UFNIA, incremental=True)
            for c in self.formula_selector.resolve_shallow_for([*a, *b]):
                solver.add_assertion(c)

            same = And(Equals(a[0], b[0]), Equals(a[1], b[1]))
            if solver.is_valid(same):
                self.implied_classes[b] = self.implied_classes[a]
    
    def solve_possible_aliasing(self):
        self.possible_aliases = { a: [] for a in self.implied_classes.values() }

        for a,b in itertools.combinations(self.possible_aliases.keys(), 2):
            solver = Solver(logic=UFNIA, incremental=True)
            for c in self.formula_selector.resolve_shallow_for([*a, *b]):
                solver.add_assertion(c)

            same = And(Equals(a[0], b[0]), Equals(a[1], b[1]))
            if solver.is_sat(same):
                self.possible_aliases[a].append(b)
                self.possible_aliases[b].append(a)
    
    def get_equivalence_classes(self) -> frozenset[tuple[frozenset[FNode], frozenset[FNode]]]:
        return frozenset([
            (
                frozenset([a for a in self.implied_classes if self.implied_classes[a] == representative]),
                frozenset(self.possible_aliases[representative]),
            )
            for representative in set(self.implied_classes.values())
        ])


class OpenVMMemoryEncoder(SingleInteractionEncoder):
    """
    Encodes memory bus interactions. It implements a permutation check on all
    interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        super().__init__()
        self.interactions = {}
        self.name_or_id = NameOrIdGenerator()
        self.analysis = None
    
    def _sorted_interactions(self) -> list[tuple[FNode, Any]]:
        return sorted(self._interactions, key=lambda i: i[1][0].size() + i[1][1].size())

    def pre_analysis(self) -> None:
        accesses = sorted(
            [(i[1][0], i[1][1]) for i in self._interactions],
            key=lambda i: i[0].size() + i[1].size()
        )
        self.analysis = MemoryAnalysis(self.constraints())
        self.analysis.solve_implied_aliasing(accesses)
        self.analysis.solve_possible_aliasing()

        if ARGS().log_memory_analysis:
            logging.warning(f"results of memory analysis")
            for access, repr in self.analysis.implied_classes.items():
                if access != repr:
                    logging.warning(f"\t{repr} == {access}")
            for access,possible in self.analysis.possible_aliases.items():
                if possible:
                    logging.warning(f"\t{access} possibly aliases with")
                    for p in possible:
                        logging.warning(f"\t\t{p}")


    def group_interactions(self):
        assert self.analysis is not None
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
                res[alias].append((interaction, False))

        return res

    def encode(self, mult: FNode, address_space: FNode, pointer: FNode, data: list[FNode], timestamp: FNode) -> FNode:
        return with_comment(
            Implies(
                #Equals(wrap_mod(mult), wrap_mod(Int(-1))),
                TRUE(),
                And(
                    *[ And(LE(Int(0), d), LE(d, Int(255))) for d in data ]
                )
            ),
            f"MEMORY interaction for {address_space} {pointer}"
        )
    
    def get_axioms(self) -> list[FNode]:
        grouped = self.group_interactions()
        encode_timestamps = lambda i1, i2: LT(i1[4], i2[4])
        return And(
            with_comment(
                encode_permutation_check(interactions, encode_timestamps),
                f"MEMORY axioms for {address_space} {pointer}"
            )
            for (address_space, pointer), interactions in grouped.items()
        )
