"""Memory bus: array-valued state chain with stores, reads, and permutation semantics."""
import itertools
import logging
from functools import lru_cache
from typing import Any

from .permutation_check import (
    PermutationCheckMixin,
    TimestampCheckMixin,
    keyed_io_relation,
)

from .single_interaction_encoder import BusInteraction, SingleInteractionEncoder

from ..smt.utils import *
from ..utils.utils import none_if
from ..membus.facts import TS_MAX


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
        # syntactic upper bounds from the constraint set, stashed by
        # `infer_unconditional_ranges` for the interface-mode limb split
        self._syntactic_bounds: dict[FNode, int] = {}

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
        pval = ARGS().field_type.value

        _align = self._cur_state.memory_bus_alignment
        _assume_is_valid = _align is not None and getattr(
            _align, "after_assume_is_valid", False
        )

        def _active_mult(idx: int) -> int | None:
            return _const_mult(self._interactions[idx].mult, pval, _assume_is_valid)

        interface = ARGS().memory_encoding == "interface"
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
            case "interface":
                # Uninterpreted-interface mode: memory semantics is not encoded
                # at all. The cross-circuit io relation equates each aligned
                # pair's full argument tuple instead (see
                # `interface_io_relation`), so no per-side permutation
                # machinery, status booleans, or match variables exist. Only
                # sound when every interaction's activation is statically
                # known — gated (is_valid) multiplicities would need status
                # resolution we deliberately do not do here (v1).
                nonconst = [
                    i
                    for i in range(len(self._interactions))
                    if _active_mult(i) not in (0, 1, pval - 1)
                ]
                if nonconst and ARGS().interface_ignore_checks:
                    # Same escape hatch as the alignment identity fallback
                    # (--interface-ignore-checks): skip the const-mult gate
                    # and let the io_relation equate the
                    # aligned pairs' argument tuples unconditionally. Only sound
                    # when aligned pairs are the same interaction (so their args
                    # coincide regardless of the gated activation).
                    logging.info(
                        "interface-ignore-checks: skipping the const-mult gate "
                        "for %d memory interaction(s) with symbolic (is_valid/flag-"
                        "gated) multiplicities; the interface io_relation will equate "
                        "aligned argument tuples WITHOUT resolving activation.",
                        len(nonconst),
                    )
                elif nonconst:
                    i = nonconst[0]
                    raise RuntimeError(
                        "interface memory encoding: mult of memory "
                        f"interaction #{i} is not const-evaluable to "
                        f"-1/0/1: {self._interactions[i].mult}"
                    )
                permutation_axioms = []
                inputs = []
                outputs = []
                intermediates = []
                isinputs = []
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
        # Key reconstruction: membus identifies each key as base+offset (a
        # trusted syntactic reading of the circuit, independent of its guessed
        # solve). Relate interactions that share a base to a common anchor:
        # `pointer_i == pointer_anchor + (offset_i - offset_anchor) (mod P)`.
        # This is a true identity (both are `base + off`), and it lets EUF/arith
        # derive key distinctness cheaply — for same-base i,j the pointers
        # differ by the constant `offset_i - offset_j`, so `key_i = key_j` folds
        # to a nonzero constant instead of z3 grinding the nonlinear limb
        # reconstruction. We anchor to an EXISTING pointer (not a fresh symbol),
        # else the fresh var gets universally quantified into a huge forall.
        key_recon = []
        alignment = self._cur_state.memory_bus_alignment
        source_path = self._cur_state.source_path
        if not interface and alignment is not None and source_path is not None:
            info = alignment.info_for(source_path)
            if len(info) == len(self._interactions):
                anchor: dict[str, tuple[FNode, int]] = {}
                for id in range(len(self._interactions)):
                    k = info[id].key
                    if (
                        k is None
                        or k.kind != "base_offset"
                        or k.base is None
                        or k.offset is None
                        or _active_mult(id) in (None, 0)
                    ):
                        continue
                    ptr = self._interactions[id].args[1]
                    if k.base not in anchor:
                        anchor[k.base] = (ptr, k.offset)
                        continue
                    aptr, aoff = anchor[k.base]
                    key_recon.append(
                        with_comment(
                            field_eq(Minus(Minus(ptr, aptr), Int(k.offset - aoff))),
                            f"membus #{id} key {k.base}+{k.offset} (anchor +{aoff})",
                        )
                    )
        # Timestamp reconstruction (analogous to key reconstruction). membus
        # recovers each interaction's clock as base T + offset (`T+k` exact for
        # sends, `<=T+k` upper for recvs). The circuit represents timestamps via
        # nonlinear less-than-gadget decompositions (`timestamp_lt_aux__
        # lower_decomp`), which z3 grinds. Relate each timestamp column to a
        # common anchor (an EXACT-time interaction, base T): exact interactions
        # get `ts_i == T_anchor + (off_i - off_anchor)`, upper (recv) ones
        # `ts_i <= T_anchor + (off_i - off_anchor)`. Raw integer (not mod)
        # comparison — sound under membus's TS_BOUND (timestamps < 2^29, no
        # wraparound). This makes timestamp differences constant so the
        # comparison-gadget constraints fold instead of z3 solving nonlinear
        # modular limb equations.
        # Timestamp bounds (TS_BOUND). Reconstruction alone anchors every
        # recognized clock to a common base T, but leaves T itself free over the
        # whole field — so the solver can pick T = p-1, wrapping `T+1` to 0 and
        # satisfying the memory less-than gadget with a phantom ordering. That
        # forges a soundness counterexample (out of every real execution, where
        # timestamps are cycle counts < 2^29 and never wrap). Assert TS_BOUND,
        # `0 <= ts < 2^29`, on each membus-recognized timestamp column — the same
        # positional set ts_recon ties together, so bounding them (base included)
        # bounds the whole clock web. Sound: it is the same assumption membus's
        # own analysis grants ([[membus/facts.py]] Assumption.TS_BOUND).
        ts_recon = []
        ts_bounds = []
        if not interface and alignment is not None and source_path is not None:
            info = alignment.info_for(source_path)
            if len(info) == len(self._interactions):
                # An interaction is active exactly when its multiplicity is
                # nonzero; the timestamp facts hold only while it is active. We
                # guard each fact by `mult != 0` -- a plain term over the stored
                # multiplicity, whatever it is -- instead of requiring the
                # multiplicity to const-evaluate. For a constant +-1 mult this
                # folds to TRUE (facts stay unguarded, unchanged); for a
                # flag-gated `+-is_valid` mult it becomes the activation
                # condition, WITHOUT the encoder having to identify or evaluate
                # the gating column. This is what makes the `is_valid` (after)
                # program emit the same ts_recon/ts_bounds the constant-mult
                # (before) program does, so soundness (which asserts is_valid=1)
                # sees a symmetric timestamp story on both sides. The send/recv
                # kind still comes from the membus analysis (`ti.kind`).
                def _active_guard(idx: int) -> FNode:
                    return Not(field_eq(self._interactions[idx].mult))

                def _guarded(guard: FNode, fact: FNode) -> FNode:
                    g = guard.simplify()
                    return fact if g.is_true() else Implies(g, fact)

                ts_anchor: tuple[FNode, int, int] | None = None
                for id in range(len(self._interactions)):
                    ti = info[id].time
                    if ti is None or ti.offset is None:
                        continue
                    if field_eq(self._interactions[id].mult).simplify().is_true():
                        continue  # multiplicity is identically 0 (disabled)
                    tcol = self._interactions[id].args[3]
                    # Bound every recognized clock independently: the field-only
                    # tie to the anchor still admits `ts = anchor + off + p` (a
                    # wrap), so bounding the anchor alone leaves phantom wrapped
                    # clocks. A per-column `< 2^29` is the sound, complete bound.
                    ts_bounds.append(
                        with_comment(
                            _guarded(
                                _active_guard(id),
                                And(LE(Int(0), tcol), LT(tcol, Int(TS_MAX))),
                            ),
                            f"ts #{id} in [0, 2^29) (TS_BOUND)",
                        )
                    )
                    if ts_anchor is None:
                        if ti.kind == "exact":  # anchor must be an exact clock
                            ts_anchor = (tcol, ti.offset, id)
                        continue
                    atcol, aoff, aidx = ts_anchor
                    rhs = Plus(atcol, Int(ti.offset - aoff))
                    # The relation ties ts_i to the anchor, so it is meaningful
                    # only when BOTH interactions are active -- guard by both.
                    guard = And(_active_guard(id), _active_guard(aidx))
                    if ti.kind == "exact":
                        ts_recon.append(
                            with_comment(_guarded(guard, field_eq(Minus(tcol, rhs))),
                                         f"ts #{id} = T+{ti.offset}")
                        )
                    else:
                        ts_recon.append(
                            with_comment(_guarded(guard, LE(tcol, rhs)),
                                         f"ts #{id} <= T+{ti.offset}")
                        )
        #yield with_comment(ts, f"{self.NAME} timestamp check")
        yield with_comment(And(*permutation_axioms), f"{self.NAME} permutation axioms")
        yield with_comment(And(*assume_bytes), f"{self.NAME} assume bytes")
        if key_recon:
            yield with_comment(And(*key_recon), f"{self.NAME} key reconstruction")
        # TS_BOUND (0 <= ts < 2^29, the same fact membus's own analysis grants,
        # [[membus/facts.py]] Assumption.TS_BOUND) is a *derived consequence* of
        # the circuit, not a commitment it makes. Route it through the
        # consequences channel, NOT the axioms channel:
        #
        #   * As a constraint it became a per-interaction proof obligation in
        #     the goal disjunction (hundreds of mod-arithmetic disjuncts, the
        #     dominant solve cost on TS_BOUND-heavy blocks) — must stay off the
        #     obligation side.
        #   * As an *axiom* it was asserted for BOTH sides at top level, i.e.
        #     OUTSIDE the ForAll. On the quantified side that binds a FREE copy
        #     of the timestamp column while the checked constraints (inside the
        #     ForAll) use the BOUND copy — the two shadow/decouple, so the bound
        #     never reaches the quantified vars, yet the free copy floats and
        #     z3 can pick it adversarially (spurious sat on is_valid soundness).
        #   * As a *consequence* it is asserted for the reference (premise) side
        #     only: it binds the timestamps that genuinely appear as free
        #     premises and introduces no free shadow copy on the checked side.
        #
        # Key/timestamp reconstruction stay committed (yielded above): equally
        # granted in principle, but routing them off-goal measurably regressed
        # 2100224 (3x assert blowup after propagate-values, unknowns on the
        # pointer-distinctness family), and as obligations they are cheap.
        if ts_bounds:
            self.consequences.append(
                Consequence(
                    ConsequenceKind.MEMORY_TIMESTAMP_BOUNDS,
                    with_comment(And(*ts_bounds), f"{self.NAME} timestamp bounds"),
                )
            )
        # Interface mode: "memory holds bytes" is a VM environment assumption
        # (like TS_BOUND), not a circuit commitment — each recv's data limbs
        # are bytes because every value in memory was range-checked when
        # written. Recvs are statically known here (const mult == p-1), so no
        # isinput booleans are needed. Routed through the consequences channel
        # (like the timestamp bounds above): a premise for the reference (before)
        # side only, never a proof obligation. The send-side
        # counterpart ("every byte written is a byte") is a per-circuit
        # property, independently recoverable by the deterministic bound
        # algorithm (`infer_unconditional_ranges`) — it must not join the
        # equivalence VC.
        # Internal (single-circuit) forced recv<->send pairs, computed early so
        # the send-byte obligation below can exclude them. "Memory holds bytes"
        # is a VM-environment invariant needed only because OTHER, later
        # consumers read memory and lean on it via the recv-bytes grant above --
        # it exists to make THAT premise sound for traffic something outside
        # this circuit can actually observe. A forced internal pair is exactly
        # the align-certified opposite: the write is immediately consumed by
        # its one forced partner recv and the whole pair is compiled away --
        # absent from `after`, hence absent from every later pass too. Nothing
        # outside this circuit ever gets a chance to read it, so nothing ever
        # relies on it being a byte; requiring it anyway was pure proof-cost
        # with no corresponding safety payoff, not a documented property of
        # the pair itself. (Team decision, 2026-08-11: block-internal,
        # unobservable memory traffic is allowed to be non-bytes.) This is
        # independent of `internal_pair_equalities` below, which still ties
        # the pair's arguments together as a real constraint -- a *misclassified*
        # pair (one that isn't actually forced/local) would surface as a
        # failure there, not here.
        internal_pairs: list[tuple[int, int]] = []
        if (
            interface
            and ARGS().interface_internal_pairs
            and alignment is not None
            and source_path is not None
        ):
            internal_pairs = alignment.internal_pairs_for(source_path)
        internal_pair_ids = {id for pair in internal_pairs for id in pair}
        if interface and ARGS().interface_assume_bytes:
            # Memory data limbs are bytes. We *assume* it for reads and *ensure*
            # it for writes:
            #   * recv (read, mult ≡ -1): ASSUME -- granted premise; the value
            #     was range-checked by whatever wrote it. Routed through the
            #     consequences channel (reference/before side only, never an
            #     obligation), like the timestamp bounds above.
            #   * send (write, mult ≡ +1): ENSURE -- a proof obligation; the
            #     circuit that writes must write bytes. Emitted as a constraint
            #     (both sides), so the before side carries it as a premise and
            #     the after side as an obligation. Sends that are the internal
            #     leg of a forced recv<->send pair are excluded (see above).
            # Guarding by mult ≡ ∓1 (instead of a const-mult test) covers
            # is_valid/flag-gated accesses too: when inactive the mult folds to 0
            # and neither guard fires -- so no byte claim is made on an inactive
            # interaction's (unconstrained) data. This mirrors the plain
            # encoding's `Implies(isinput, bytes)`, where the permutation's input
            # flag is exactly `mult ≡ -1`. (Prototype: the old code only granted
            # recv bytes for statically-const recvs, missing gated reads like the
            # branch-flag-gated rs1/rs2 register reads -- the source of the
            # spurious `a__3_12 = 256` completeness counterexample.)
            def _data_are_bytes(id):
                return And(
                    *[
                        And(LE(Int(0), wrap_mod(d)), LE(wrap_mod(d), Int(255)))
                        for d in self._interactions[id].args[2]
                    ]
                )

            def _is_recv(id):  # mult ≡ -1 (mod p)
                return Equals(
                    wrap_mod(Plus(self._interactions[id].mult, Int(1))), Int(0)
                )

            def _is_send(id):  # mult ≡ +1 (mod p)
                return Equals(
                    wrap_mod(Minus(self._interactions[id].mult, Int(1))), Int(0)
                )

            ids_with_data = [
                id
                for id in range(len(self._interactions))
                if self._interactions[id].args[2]
            ]
            recv_bytes = [
                with_comment(
                    Implies(_is_recv(id), _data_are_bytes(id)),
                    f"membus #{id} recv data are bytes if active (granted)",
                )
                for id in ids_with_data
            ]
            if recv_bytes:
                grant = with_comment(
                    And(*recv_bytes), f"{self.NAME} recv byte assumption"
                )
                self.consequences.append(
                    Consequence(ConsequenceKind.MEMORY_RECV_BYTES, grant)
                )
            send_bytes = [
                with_comment(
                    Implies(_is_send(id), _data_are_bytes(id)),
                    f"membus #{id} send data are bytes if active (ensured)",
                )
                for id in ids_with_data
                if id not in internal_pair_ids
            ]
            if send_bytes:
                yield with_comment(
                    And(*send_bytes), f"{self.NAME} send byte obligation"
                )
        # Internal (single-circuit) forced recv<->send pairs: memory is a
        # deterministic environment, so a recv whose forced source is a local
        # send reads exactly what that send wrote — equate the full argument
        # tuples (the recv's ts slot holds prev_timestamp, so recv.prev_ts ==
        # send.ts falls out positionally). Justified by membus align's
        # certification that the connection is FORCED — entailed under every
        # aliasing resolution — and re-verified in `preanalysis`.
        #
        # Emitted as circuit CONSTRAINTS (a circuit transformation: C' = C AND
        # eqs, after which the pair is compiled away and the busses align),
        # NOT through the granted-axioms channel. Polarity: as a constraint,
        # the equality is a premise when this circuit sits in the outer
        # (forall) position and an obligation at the skolem witness when it
        # sits in the inner (exists) position — a corrupted dump whose
        # substituted values disagree with the pair fails the obligation and
        # the check comes back SAT. As a granted axiom it instead contradicted
        # the other side's constraints through the same-name pins AT TOP LEVEL,
        # making the whole soundness artifact vacuously unsat — a false PASS
        # (measured on 2099600 010->011 with a corrupted send literal).
        if internal_pairs:
            eqs = internal_pair_equalities(
                self.NAME, self._bus_interactions(), internal_pairs, _assume_is_valid
            )
            logging.info(
                "%s interface internal pairs: %d pair(s) -> %d equalities",
                self.NAME,
                len(internal_pairs),
                len(eqs),
            )
            yield with_comment(
                And(*eqs), f"{self.NAME} internal pair equalities"
            )
        if ts_recon:
            yield with_comment(And(*ts_recon), f"{self.NAME} timestamp reconstruction")

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
            m = wrap_mod(self._interactions[i].mult).simplify()
            return m.constant_value() % p if m.is_int_constant() else None

        mults = [const_mult(i) for i in range(n)]
        datas = [self._interactions[i].args[2] for i in range(n)]

        # Per-interaction membus timestamp offset (from T). Sends carry an
        # exact offset, recvs an upper bound. Used to sever a recv from any
        # send that is not strictly earlier: a read can only return a value
        # written by a prior write. For symbolic-key (AS2) cells this is the
        # only thing that severs recv<->send, turning the otherwise-cyclic
        # "all sends must be bounded" dependency into a well-founded temporal
        # order so the fixpoint can bound reads inductively. Relies on the
        # membus TS_BOUND assumption (timestamps do not wrap mod p).
        alignment = self._cur_state.memory_bus_alignment
        source_path = self._cur_state.source_path
        ts_off: list[int | None] = [None] * n
        if alignment is not None and source_path is not None:
            info = alignment.info_for(source_path)
            if len(info) == n:
                ts_off = [
                    x.time.offset if x.time is not None else None for x in info
                ]

        def flat_args(i: int) -> list[FNode]:
            a, ptr, data, t = self._interactions[i].args
            return [a, ptr, *data, t]

        def _ts_severed(i: int, j: int) -> bool:
            """True if a recv/send pair cannot match on timestamp order.

            A recv (``mult == p-1``) can only match a send (``mult == 1``)
            whose exact time is strictly before the recv's (upper-bound) time.
            """
            if mults[i] == p - 1 and mults[j] == 1:
                recv, send = i, j
            elif mults[i] == 1 and mults[j] == p - 1:
                recv, send = j, i
            else:
                return False
            r, s = ts_off[recv], ts_off[send]
            return r is not None and s is not None and s >= r

        @lru_cache(maxsize=None)
        def cannot_match(i: int, j: int) -> bool:
            """``m(i, j)`` is statically impossible.

            Matching forces every arg pair equal mod p; if any pair
            differs by a nonzero constant (distinct pointer constants, or
            ``T + c1`` vs ``T + c2`` timestamps), the case is dead. This
            is what severs a read from its own write-back half, whose
            data is the same unranged column. A recv is also severed from
            any send that is not strictly earlier in time (see ``_ts_severed``).
            """
            if mults[i] is not None and mults[j] is not None and (mults[i] + mults[j]) % p != 0:
                return True
            if _ts_severed(i, j):
                return True
            for x, y in zip(flat_args(i), flat_args(j)):
                if x == y:
                    continue
                if x.is_int_constant() and y.is_int_constant():
                    if (x.constant_value() - y.constant_value()) % p != 0:
                        return True
                    continue
                if x.is_symbol() and y.is_symbol():
                    continue
                d = wrap_mod(Minus(x, y)).simplify()
                if d.is_int_constant() and d.constant_value() % p != 0:
                    return True
            return False

        base = self._collect_syntactic_bounds(all_constraints)
        self._syntactic_bounds = base

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
        read_total = sum(len(datas[i]) for i in range(n) if mults[i] == p - 1)
        read_bounded = sum(
            1
            for i in range(n)
            if mults[i] == p - 1
            for k in range(len(datas[i]))
            if bound[(i, k)] is not None
        )
        logging.info(
            "%s range inference: %d base bounds, %d/%d limbs bounded, "
            "%d/%d read limbs bounded, %d facts emitted",
            self.NAME,
            len(base),
            sum(1 for v in bound.values() if v is not None),
            len(bound),
            read_bounded,
            read_total,
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
        if ARGS().memory_encoding == "interface":
            alignment = self._cur_state.memory_bus_alignment
            if alignment is None:
                raise RuntimeError(
                    "interface memory encoding requires a membus alignment"
                )
            # kept_pairs, not before_to_after: only the genuine align "kept"
            # rows (never the identity fill). The removed interactions (internal
            # pair legs + inert rows) are the certified remainder — their
            # equalities live on their own side (see `internal_pair_equalities`).
            internal_a = alignment.removed_for(alignment.before_path)
            return interface_io_relation(
                f"IO RELATION for {self.NAME}",
                self._bus_interactions(),
                other._bus_interactions(),
                alignment.kept_pairs,
                bounds_a=self._syntactic_bounds,
                bounds_b=other._syntactic_bounds,
                internal_a=internal_a,
                assume_is_valid=getattr(
                    alignment, "after_assume_is_valid", False
                ),
            )
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


LIMB_BASE = 65536  # pointers are packed as l0 + 65536*l1 (two 16-bit limbs)


def _bound_of(t: FNode, bounds: dict[FNode, int]) -> int | None:
    """Proven upper bound for `t`'s FIELD VALUE, if any (cf. `base_bound`).

    Besides direct facts on ``t`` / ``wrap_mod(t)``, recognizes SCALED range
    checks ``(c*t mod P) <= hi`` (e.g. OpenVM's pointer-alignment check
    ``(4^{-1}*ptr_lo mod P) < 2^14``): the only field values ``v`` with
    ``(c*v mod P) <= hi`` are ``v = d*k`` for ``k <= hi`` where ``d = c^{-1}
    mod P`` — provided ``d*hi < P`` (no wrap), so ``v <= d*hi``.

    Raw (non-mod) facts ``t <= hi`` are trusted as field-value bounds; every
    producer in the constraint set is a range-check encoder that emits the
    two-sided ``0 <= t <= hi`` form.
    """
    if t.is_int_constant():
        return t.constant_value()
    best = bounds.get(wrap_mod(t), bounds.get(t))
    p = ARGS().field_type.value
    for key, hi in bounds.items():
        if not key.is_mod():
            continue
        lf = linear_form(key.arg(0))
        if lf is None:
            continue
        terms, const = lf
        if const != 0 or len(terms) != 1:
            continue
        ((t_node, c_raw),) = terms.items()
        if t_node != t:
            continue
        c = c_raw % p
        if c == 0:
            continue
        d = pow(c, -1, p)
        if d * hi < p:
            best = d * hi if best is None else min(best, d * hi)
    return best


def _interface_pointer_eq(
    x: FNode, y: FNode, bounds_a: dict[FNode, int], bounds_b: dict[FNode, int]
) -> list[FNode] | None:
    """Split a packed-pointer equality into per-limb equalities, if sound.

    When both sides are syntactically ``l0 + LIMB_BASE*l1 + c`` (same constant
    ``c``) and, ON EACH SIDE, the proven bounds give ``l0 < LIMB_BASE`` and
    ``l0 + LIMB_BASE*l1 + c < P``, the packing is injective into ``[0, P)``,
    so the packed mod-p equality is *equivalent* to ``l0 = l0' AND l1 = l1'``
    — the replacement is sound in both proof directions. Note ``l0, l1 <
    LIMB_BASE`` alone is NOT enough: a full 32-bit packed value exceeds
    BabyBear P and wraps. Returns ``None`` when the shape or the bounds do
    not justify the split (caller falls back to the packed equality).
    """

    def parse(e: FNode, bounds: dict[FNode, int]) -> tuple[FNode, FNode, int] | None:
        lf = linear_form(e)
        if lf is None:
            return None
        terms, const = lf
        if len(terms) != 2 or sorted(terms.values()) != [1, LIMB_BASE]:
            return None
        lo = next(t for t, c in terms.items() if c == 1)
        hi = next(t for t, c in terms.items() if c == LIMB_BASE)
        b_lo, b_hi = _bound_of(lo, bounds), _bound_of(hi, bounds)
        if b_lo is None or b_hi is None or b_lo >= LIMB_BASE:
            return None
        if b_lo + LIMB_BASE * b_hi + const >= ARGS().field_type.value:
            return None
        return lo, hi, const

    px = parse(x, bounds_a)
    py = parse(y, bounds_b)
    if px is None or py is None or px[2] != py[2]:
        return None
    return [field_eq(px[0], py[0]), field_eq(px[1], py[1])]


def _const_mult(mult: FNode, p: int, assume_is_valid: bool = False) -> int | None:
    """Const-evaluate a memory multiplicity mod p, or None if not constant.

    [is_valid=1 interface] When ``assume_is_valid`` (the analysis assumed the
    openvm is_valid activation selector == 1), is_valid columns are folded to 1
    first, so a gated ``0 - is_valid`` const-evaluates to ``p - 1`` (i.e. -1).
    Remove the ``assume_is_valid`` handling once the interface encoder resolves
    is_valid-gated mults natively."""
    if assume_is_valid:
        subs = {
            v: Int(1)
            for v in mult.get_free_variables()
            if "is_valid" in v.symbol_name()
        }
        if subs:
            mult = mult.substitute(subs)
    m = wrap_mod(mult).simplify()
    return m.constant_value() % p if m.is_int_constant() else None


def internal_pair_equalities(
    name: str,
    interactions: list[BusInteraction],
    pairs: list[tuple[int, int]],
    assume_is_valid: bool = False,
) -> list[FNode]:
    """Equalities compiling away a circuit's internal forced recv<->send pairs.

    Both legs live in ONE circuit; their multiplicities cancel numerically
    (1 + (P-1) == 0 mod P), so no mult equality is needed — instead the mults
    are re-checked here as a guard. Every argument is equated positionally
    over the full tuple [addr_space, pointer, *data, timestamp] — the memkeys
    are just data from the bus perspective, and the recv's timestamp slot
    holds its prev_timestamp, so recv.prev_ts == send.ts is the positional
    equality. Field equalities throughout: the expressions feeding the membus
    are not normalized, so syntactic Int `=` would be unsound.

    ``pairs`` are unordered ordinal pairs (the recv/send roles are erased once
    the match analysis resolves both legs); recv (mult -1) and send (mult +1)
    are recovered here from the multiplicities, which doubles as the guard.
    """
    p = ARGS().field_type.value

    def cmult(inter: BusInteraction) -> int | None:
        return _const_mult(inter.mult, p, assume_is_valid)

    parts: list[FNode] = []
    for a, b in pairs:
        ia, ib = interactions[a], interactions[b]
        ma, mb = cmult(ia), cmult(ib)
        if (ma, mb) == (p - 1, 1):
            recv, send = ia, ib
        elif (mb, ma) == (p - 1, 1):
            recv, send = ib, ia
        else:
            raise RuntimeError(
                f"interface internal pair ({a},{b}): mults are "
                f"not (recv -1, send +1): {ia.mult} vs {ib.mult}"
            )
        for k, (x, y) in enumerate(zip(recv.args, send.args, strict=True)):
            parts.append(
                with_comment(
                    field_eq(x, y),
                    f"{name}: internal pair ({a},{b}) arg {k}",
                )
            )
    return parts


def interface_io_relation(
    name: str,
    interactions_a: list[BusInteraction],
    interactions_b: list[BusInteraction],
    aligned_pairs: dict[int, int],
    *,
    bounds_a: dict[FNode, int],
    bounds_b: dict[FNode, int],
    internal_a: frozenset[int] = frozenset(),
    assume_is_valid: bool = False,
) -> tuple[FNode, frozenset[FNode]]:
    """Cross-circuit io relation for the uninterpreted-interface encoding.

    Memory is treated as an external deterministic environment: two circuits
    are equivalent iff they exchange identical traffic with it. For each
    aligned pair, equate the multiplicity and the full argument tuple
    (addr_space, pointer, data limbs, timestamp). In the ForAll-position of
    the VC this yields exactly the rely/guarantee reading: equalities on free
    columns (recv data) become skolem witness pins, equalities on computed
    columns (send data) remain proof obligations. No memory semantics
    (permutation, counting, ordering) is encoded — it is only ever needed to
    justify interaction *removals*, and the alignment precondition (checked in
    `preanalysis`) guarantees the only unaligned interactions are the internal
    forced pairs in ``internal_a`` (compiled away by
    `internal_pair_equalities` on their own side) plus inert rows.
    """
    p = ARGS().field_type.value
    n, m = len(interactions_a), len(interactions_b)
    if (
        set(aligned_pairs.keys()) & internal_a
        or set(aligned_pairs.keys()) | internal_a != set(range(n))
        or sorted(aligned_pairs.values()) != list(range(m))
    ):
        raise RuntimeError(
            f"interface memory encoding: aligned pairs + internal legs are not "
            f"a disjoint cover with a 1:1 kept map ({len(aligned_pairs)} pairs "
            f"+ {len(internal_a)} internal for {n} before / {m} after)"
        )

    def cmult(inter: BusInteraction) -> int | None:
        return _const_mult(inter.mult, p, assume_is_valid)

    parts: list[FNode] = []
    splits = applied = 0
    if ARGS().interface_ignore_checks:
        _bad = [
            (i, j)
            for i, j in aligned_pairs.items()
            if cmult(interactions_a[i]) is None
            or cmult(interactions_b[j]) is None
            or cmult(interactions_a[i]) != cmult(interactions_b[j])
        ]
        if _bad:
            # Kept at WARNING (the others are info): fires once per verification
            # when --interface-ignore-checks actually bypassed a check.
            logging.warning(
                "interface-ignore-checks: %d/%d aligned pair(s) have "
                "non-const/mismatched (is_valid/flag-gated) mults; equating mult "
                "and args UNCONDITIONALLY (no gated-status resolution -- may make "
                "the obligation stronger than reality for inactive interactions).",
                len(_bad),
                len(aligned_pairs),
            )
    for i, j in sorted(aligned_pairs.items()):
        ia, ib = interactions_a[i], interactions_b[j]
        ma, mb = cmult(ia), cmult(ib)
        if ma is None or mb is None or ma != mb:
            if not ARGS().interface_ignore_checks:
                raise RuntimeError(
                    f"interface memory encoding: aligned pair ({i},{j}) mult "
                    f"mismatch or non-const: {ia.mult} vs {ib.mult}"
                )
            # Trust the pair: treat as active so the mult+arg equalities below are
            # emitted (the mult equality itself pins before-mult == after-mult).
            ma = mb = 1
        if ma == 0:
            continue  # disabled pair: no traffic, args unconstrained
        parts.append(
            with_comment(field_eq(ia.mult, ib.mult), f"{name}: pair ({i},{j}) mult")
        )
        for k, (x, y) in enumerate(zip(ia.args, ib.args, strict=True)):
            if k == 1 and ARGS().interface_limb_split:
                splits += 1
                limb_eqs = _interface_pointer_eq(x, y, bounds_a, bounds_b)
                if limb_eqs is not None:
                    applied += 1
                    parts.extend(
                        with_comment(eq, f"{name}: pair ({i},{j}) ptr limb {li}")
                        for li, eq in enumerate(limb_eqs)
                    )
                    continue
            parts.append(
                with_comment(field_eq(x, y), f"{name}: pair ({i},{j}) arg {k}")
            )
    if ARGS().interface_limb_split:
        logging.info(
            "interface io relation: limb split applied on %d/%d pointers",
            applied,
            splits,
        )
        if splits and not applied and not bounds_a and not bounds_b:
            logging.warning(
                "interface limb split: no syntactic bounds available "
                "(--skip-range-inference?); falling back to packed equalities"
            )
    return (And(*parts) if parts else TRUE(), frozenset())
