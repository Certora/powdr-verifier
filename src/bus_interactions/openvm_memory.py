from typing import Any

from .permutation_check import encode_permutation_check

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt_utils import *

class MemoryAnalysis:
    def __init__(self, constraints: list[FNode]):
        self.representatives = []
        self.belongs_to = {}
        self.solver = SolverFor(logic=QF_UFNIA)
        for c in constraints:
            self.solver.add(c)
    
    def add_memory_access(self, address_space: FNode, pointer: FNode):
        if (address_space, pointer) in self.belongs_to:
            return
        implied = []
        possibly = []

        for rid,(ras,rp) in enumerate(self.representatives):
            same = And(Equals(ras, address_space), Equals(rp, pointer))
            if is_valid(self.solver, same):
                # aliasing is implied
                print(f"aliasing is implied for {same}")
                implied.append(rid)
                break
            elif is_sat(self.solver, same):
                # aliasing is possible
                print(f"aliasing is possible for {same}")
                possibly.append(rid)

        if implied:
            # a single implied alias is found
            assert len(implied) == 1, "Multiple implied aliases for the same memory access"
            assert len(possibly) == 0, "Implied alias and possible aliases for the same memory access"
            self.belongs_to[(address_space, pointer)] = implied[0]
        elif possibly:
            # one or more possible aliases are found
            rid = len(self.representatives)
            self.representatives.append((address_space, pointer))
            self.belongs_to[(address_space, pointer)] = [rid] + possibly
        else:
            # no aliases are found
            rid = len(self.representatives)
            self.representatives.append((address_space, pointer))
            self.belongs_to[(address_space, pointer)] = rid


class OpenVMMemoryEncoder(SingleInteractionEncoder):
    """
    Encodes memory bus interactions. It implements a permutation check on all
    interactions and requires their timestamps increase.
    """
    def __init__(self) -> None:
        super().__init__()
        self.interactions = {}
        self.name_or_id = NameOrIdGenerator()
    
    def _sorted_interactions(self) -> list[tuple[FNode, Any]]:
        return sorted(self._interactions, key=lambda i: size(i[1][0]) + size(i[1][1]))

    def pre_analysis(self) -> None:
        print(f"#constraints: {len(self.constraints())}")
        #m = MemoryAnalysis(self.constraints())
        #for mult, args in self._sorted_interactions():
        #    address_space, pointer, *data, timestamp = args
        #    m.add_memory_access(address_space, pointer)
        #
        #print(m.representatives)
        #print(m.belongs_to)


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
        encode_timestamps = lambda i1, i2: LT(i1[4], i2[4])
        return And(
            with_comment(
                encode_permutation_check(interactions, encode_timestamps),
                f"MEMORY axioms for {address_space} {pointer}"
            )
            for (address_space, pointer), interactions in self.interactions.items()
        )
