"""Boundary-stopped cone-of-influence slicing over a fixed constraint list.

Checker-side sibling of ``bus_interactions.memory_plain_utils.
cone_of_influence_via_frontier``, with two differences: the frontier
convention is inverted (here ``boundary`` is the set of variables the cone
does NOT propagate through; there ``frontier_vars`` is the set it may
propagate through), and the fixpoint runs over an inverted var->constraint
index so it scales to ~18k constraints x ~16k seeds. The encoder-side helper
is left untouched.

Soundness note for callers: a slice is always a subset of the constraint
list, so ``slice ∧ d`` unsat implies ``constraints ∧ d`` unsat. The converse
does not hold -- sat on a slice proves nothing.
"""
import re
from collections import defaultdict
from typing import Iterable

from ..smt.utils import *


def boundary_vars(constraints: Iterable[FNode], pattern: re.Pattern) -> frozenset[FNode]:
    """All free variables of ``constraints`` whose name matches ``pattern`` (searched)."""
    found = set()
    for c in constraints:
        for v in c.get_free_variables():
            if v not in found and pattern.search(v.symbol_name()):
                found.add(v)
    return frozenset(found)


class ConstraintIndex:
    """Inverted variable->constraint index with a boundary-stopped COI fixpoint.

    ``boundary`` variables never join the expansion frontier: a constraint
    touching the frontier is always picked, but growth continues only through
    its non-boundary variables. This is the exact fixpoint validated by the
    2026-07-12 sliced-checker probes (``coi_complete.py::slice_idx``).
    """

    def __init__(self, constraints: list[FNode], boundary: frozenset[FNode]):
        self.constraints = constraints
        self.boundary = boundary
        self.free_vars: list[frozenset[FNode]] = [
            frozenset(c.get_free_variables()) for c in constraints
        ]
        self.var2c: dict[FNode, list[int]] = defaultdict(list)
        for i, fvs in enumerate(self.free_vars):
            for v in fvs:
                self.var2c[v].append(i)
        # The "memory argument": every constraint that touches a boundary var.
        self.mem_indices: frozenset[int] = frozenset(
            i for i, fvs in enumerate(self.free_vars) if not boundary.isdisjoint(fvs)
        )

    def slice_seed(self, formula: FNode) -> frozenset[FNode]:
        """The non-boundary free vars of ``formula`` -- the part of the seed that
        can expand the cone. Boundary seed vars never contribute (they enter
        ``active`` but not the frontier), so this is a complete cache key for
        :meth:`slice_indices`."""
        return frozenset(v for v in formula.get_free_variables() if v not in self.boundary)

    def slice_indices(self, seed_vars: Iterable[FNode]) -> frozenset[int]:
        """Indices of constraints in the boundary-stopped COI of ``seed_vars``."""
        picked: set[int] = set()
        active = set(seed_vars)
        frontier = {v for v in active if v not in self.boundary}
        while frontier:
            new_frontier: set[FNode] = set()
            for v in frontier:
                for i in self.var2c.get(v, ()):
                    if i in picked:
                        continue
                    picked.add(i)
                    for w in self.free_vars[i]:
                        if w not in active:
                            active.add(w)
                            if w not in self.boundary:
                                new_frontier.add(w)
            frontier = new_frontier
        return frozenset(picked)
