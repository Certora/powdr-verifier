"""Memory bus: array-valued state chain with stores, reads, and permutation semantics."""
import itertools
import logging
from typing import Any

from .permutation_check import (
    PermutationCheckMixin,
    TimestampCheckMixin,
    keyed_io_relation,
)

from .single_interaction_encoder import BusInteraction, SingleInteractionEncoder

from ..smt.utils import *
from ..utils.utils import none_if


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
    TIMESTAMPED = True
    STATEFUL = True

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
        if ARGS().memory_encoding == "none":
            return TRUE()
        if address_space.is_int_constant() and address_space.constant_value() == 0:
            assert mult.is_int_constant() and mult.constant_value() == 0, f"mult is {mult}, {address_space}, {pointer}"
        return Implies(
            And(
                Equals(wrap_mod(Plus(mult, Int(1))), Int(0)),
                Equals(wrap_mod(address_space), Int(1)),
                Equals(wrap_mod(pointer), Int(0)),
            ),
            And(*[Equals(wrap_mod(d), Int(0)) for d in data]),
        )
        return with_comment(
            Implies(
                # Equals(wrap_mod(mult), wrap_mod(Int(-1))),
                TRUE(),
                And(*[And(LE(Int(0), d), LE(d, Int(255))) for d in data]),
            ),
            f"MEMORY interaction for {address_space} {pointer}",
        )

    @none_if(lambda: ARGS().no_memory)
    def encode_all(self) -> Iterable[FNode]:
        """Return timestamp + array-based permutation axioms for the memory bus."""
        ts = self.ordered_timestamp_check()
        match ARGS().memory_encoding:
            case "array":
                permutation_axioms, inputs, intermediates, outputs, isinputs = (
                    self.array_permutation_check(
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
                        interactions=[
                            BusInteraction(mult, [a, p, *args, t])
                            for mult, (a, p, args, t) in self._interactions
                        ],
                        is_memory=True,
                    )
                )
            case "plain":
                bus_interactions = [
                    BusInteraction(mult, [a, p, *args, t])
                    for mult, (a, p, args, t) in self._interactions
                ]
                permutation_axioms, isinputs, isoutputs = self.plain_permutation_check(
                    interactions=bus_interactions,
                )
                self._isinputs = isinputs
                self._isoutputs = isoutputs
                inputs = []
                outputs = []
                intermediates = []
            case "none":
                permutation_axioms = []
                inputs = []
                outputs = []
                intermediates = []
                isinputs = []
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
                            And(LE(Int(0), wrap_mod(d)), LE(wrap_mod(d), Int(255)))
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

    def _bus_interactions(self) -> list[BusInteraction]:
        return [
            BusInteraction(mult, [a, p, *args, t])
            for mult, (a, p, args, t) in self._interactions
        ]

    @staticmethod
    def _collect_syntactic_bounds(all_constraints: list[FNode]) -> dict[FNode, int]:
        """Map terms to proven unconditional upper bounds, syntactically.

        Walks each constraint: descends conjunctions, folds ``Implies``
        whose antecedent simplifies to a constant (the range-checking
        encoders guard their facts with ``mult != 0``, which folds away
        when the multiplicity is a constant). Collects ``t <= c`` /
        ``t < c`` with constant ``c``; keys are the bounded terms as-is
        (typically ``(mod e p)`` nodes from ``wrap_mod``).
        """
        bounds: dict[FNode, int] = {}

        def visit(f: FNode) -> None:
            if f.is_and():
                for a in f.args():
                    visit(a)
                return
            if f.is_implies():
                guard = f.arg(0).simplify()
                if guard.is_true():
                    visit(f.arg(1))
                return
            if f.is_le() or f.is_lt():
                t, c = f.args()
                if c.is_int_constant():
                    hi = c.constant_value() - (1 if f.is_lt() else 0)
                    bounds[t] = min(bounds.get(t, hi), hi)

        for c in all_constraints:
            visit(c)
        return bounds

    def infer_unconditional_ranges(
        self, all_constraints: list[FNode]
    ) -> list[FNode]:
        """Derive unconditional ranges for plain-encoding data limbs.

        Case-join over the plain permutation matching: in every model, an
        interaction's data limb is either covered by the input byte
        assumption (``assume_bytes``), or equal (mod p) to the data of a
        match partner whose limb is itself in range. The base of the
        derivation is read off syntactically, never assumed: the
        range-checking encoders (bitwise lookup, variable / tuple range
        checkers) emit their facts directly into the constraint list, and
        :meth:`_collect_syntactic_bounds` picks up exactly those whose
        guard is statically true. Reads then inherit bounds by least
        fixpoint over their possible match partners (case-join =
        ``max`` over cases, with the input case contributing 255); limbs
        sharing the same term propagate to each other, which covers
        write-data-is-an-earlier-read-column chains.

        Every emitted fact is a logical consequence of the existing
        constraint set — a lemma. It saves the solver from re-deriving
        the range through the matching case split at search time, which
        is what makes e.g. EqualZeroCheck bridging tractable (byte sums
        satisfy ``sum != 0 mod p`` iff some byte is nonzero only under
        these ranges).

        Interactions whose multiplicity is not a nonzero constant are
        skipped: a potentially-disabled interaction has unconstrained
        data, so no unconditional fact holds for it.
        """
        n = len(self._interactions)
        if n == 0:
            return []

        p = ARGS().field_type.value
        INPUT_BOUND = 255  # assume_bytes: inputs are byte-decomposed

        def const_mult(i: int) -> int | None:
            m = self._interactions[i].mult
            return m.constant_value() % p if m.is_int_constant() else None

        mults = [const_mult(i) for i in range(n)]
        datas = [self._interactions[i].args[2] for i in range(n)]

        def flat_args(i: int) -> list[FNode]:
            a, ptr, data, t = self._interactions[i].args
            return [a, ptr, *data, t]

        def cannot_match(i: int, j: int) -> bool:
            """``m(i, j)`` is statically impossible.

            Matching forces every arg pair equal mod p; if any pair
            differs by a nonzero constant (distinct pointer constants, or
            ``T + c1`` vs ``T + c2`` timestamps), the case is dead. This
            is what severs a read from its own write-back half, whose
            data is the same unranged column.
            """
            if mults[i] is not None and mults[j] is not None and (mults[i] + mults[j]) % p != 0:
                return True
            for x, y in zip(flat_args(i), flat_args(j)):
                d = wrap_mod(Minus(x, y)).simplify()
                if d.is_int_constant() and d.constant_value() % p != 0:
                    return True
            return False

        base = self._collect_syntactic_bounds(all_constraints)

        def base_bound(d: FNode) -> int | None:
            b = base.get(wrap_mod(d), base.get(d))
            if d.is_int_constant():
                v = d.constant_value() % p
                b = v if b is None else min(b, v)
            return b

        # bound[(i, k)]: limb k of interaction i is in [0, bound] in every model
        bound: dict[tuple[int, int], int | None] = {
            (i, k): base_bound(d)
            for i in range(n)
            for k, d in enumerate(datas[i])
        }

        def join(*cases: int | None) -> int | None:
            """Bound holding in all cases: max, None if any case is unbounded."""
            return None if any(c is None for c in cases) else max(cases)

        def meet(a: int | None, b: int | None) -> int | None:
            """Tightest of two bounds for the same limb."""
            return a if b is None else b if a is None else min(a, b)

        def run_fixpoint() -> None:
            changed = True
            while changed:
                changed = False
                # limbs naming the same term share their bounds
                by_term: dict[FNode, int | None] = {}
                for i in range(n):
                    for k, d in enumerate(datas[i]):
                        by_term[d] = meet(by_term.get(d), bound[(i, k)])
                for i in range(n):
                    if mults[i] is None or mults[i] == 0:
                        continue  # may be disabled => data unconstrained
                    for k, d in enumerate(datas[i]):
                        new = meet(bound[(i, k)], by_term[d])
                        if mults[i] == p - 1:
                            # cases: self-match as input (assumed bytes), or
                            # a pair match with j (limb equal mod p to j's)
                            partners = [
                                bound[(j, k)] if k < len(datas[j]) else None
                                for j in range(n)
                                if j != i and not cannot_match(i, j)
                            ]
                            new = meet(new, join(INPUT_BOUND, *partners))
                        if new != bound[(i, k)]:
                            bound[(i, k)] = new
                            changed = True

        run_fixpoint()

        out = []
        emitted: dict[FNode, int] = {}
        for (i, k), hi in sorted(bound.items(), key=lambda x: x[0]):
            d = datas[i][k]
            if hi is None or d.is_int_constant():
                continue
            if base_bound(d) is not None and base_bound(d) <= hi:
                continue  # already syntactically present
            if emitted.get(d, p) <= hi:
                continue
            emitted[d] = hi
            w = wrap_mod(d)
            out.append(
                with_comment(
                    And(LE(Int(0), w), LE(w, Int(hi))),
                    f"RANGE INFERENCE: {self.NAME} interaction {i} data limb {k}",
                )
            )
        logging.info(
            "%s range inference: %d base bounds, %d/%d limbs bounded, %d facts emitted",
            self.NAME,
            len(base),
            sum(1 for v in bound.values() if v is not None),
            len(bound),
            len(out),
        )
        for (i, k), hi in sorted(bound.items()):
            logging.debug(
                "range inference limb (%d,%d) mult=%s bound=%s expr=%s",
                i, k, mults[i], hi, datas[i][k],
            )
        return out

    def build_io_relation(
        self, other: SingleInteractionEncoder
    ) -> tuple[FNode, frozenset[FNode]]:
        if ARGS().memory_encoding == "none":
            return (TRUE(), frozenset())
        if ARGS().memory_encoding == "plain":
            alignment = self._cur_state.memory_bus_alignment
            return keyed_io_relation(
                f"IO RELATION for {self.NAME}",
                self._bus_interactions(),
                other._bus_interactions(),
                self._isinputs,
                self._isoutputs,
                other._isinputs,
                other._isoutputs,
                xmatch_name_prefix=self.NAME,
                aligned_pairs=(
                    alignment.before_to_after if alignment is not None else None
                ),
            )
        return super().build_io_relation(other)
