"""Mixins and formulas for multiset permutation invariants and timestamp monotonicity."""
import collections
from dataclasses import dataclass
from itertools import batched, pairwise
import itertools
import logging
from pathlib import Path
from typing import Any, Callable

from .memory_plain_utils import (
    boolean_propagate,
    plain_memory_const_key_io_hints,
    plain_memory_presolve_incremental,
    plain_memory_presolve_individual,
)
from ..verify.membus_types import AlignRowInfo, MembusAlignment, parse_membus_key
from ..smt.utils import *
from ..utils.args import ARGS
from ..utils.enums import MemoryPresolve
from ..utils.stats import profile


@dataclass
class PlainPermutationIo:
    """Plain-encoding I/O flags and match vars after static kills (symbols or constants)."""

    is_inputs: list[FNode]
    is_outputs: list[FNode]
    is_disableds: list[FNode]
    match_vars: dict[tuple[int, int], FNode]


def _plain_static_profile(
    interactions: list,
    p: int,
) -> tuple[list[int | None], list[tuple[int | None, ...] | None]]:
    """Per interaction: constant multiplicity mod p (or None) and per-limb constants."""
    mult_const: list[int | None] = []
    const_args: list[tuple[int | None, ...] | None] = []
    for inter in interactions:
        m = inter.mult
        mult_const.append(m.constant_value() % p if m.is_int_constant() else None)
        raw = inter.args
        flat: list[FNode] = (
            raw
            if isinstance(raw, list)
            else [raw[0], raw[1], *raw[2], raw[3]]
        )
        row = tuple(
            x.constant_value() % p if x.is_int_constant() else None
            for x in flat
        )
        const_args.append(None if not any(v is not None for v in row) else row)
    return mult_const, const_args


def _plain_pairwise_match_impossible_static(
    i: int,
    j: int,
    mult_const: list[int | None],
    const_args: list[tuple[int | None, ...] | None],
    p: int,
) -> bool:
    """True when ``m(i,j)`` cannot hold: mult or arg data statically incompatible."""
    mi, mj = mult_const[i], mult_const[j]
    ai, aj = const_args[i], const_args[j]
    if mi is None and mj is None and (ai is None or aj is None):
        return False
    if mi == 0 or mj == 0:
        return True
    if mi is not None and mj is not None and (mi + mj) % p != 0:
        return True
    if ai is not None and aj is not None:
        for vi, vj in zip(ai, aj, strict=True):
            if vi is not None and vj is not None and vi != vj:
                return True
    return False


def _membus_ordered_ts_pairs(order_edges: list[dict]) -> set[frozenset[str]]:
    """Pairs of abstract timestamps with a strict order (transitive closure of edges)."""
    nodes = sorted({e["lhs"] for e in order_edges} | {e["rhs"] for e in order_edges})
    if not nodes:
        return set()
    idx = {n: i for i, n in enumerate(nodes)}
    n = len(nodes)
    before = [[False] * n for _ in range(n)]
    for e in order_edges:
        before[idx[e["lhs"]]][idx[e["rhs"]]] = True
    for k in range(n):
        for i in range(n):
            if not before[i][k]:
                continue
            for j in range(n):
                before[i][j] = before[i][j] or before[k][j]
    return {
        frozenset({nodes[i], nodes[j]})
        for i in range(n)
        for j in range(i + 1, n)
        if before[i][j] or before[j][i]
    }


def _preset_force_self(presets: dict[tuple[int, int], bool], n: int, i: int) -> None:
    presets[(i, i)] = True
    for j in range(i):
        presets[(j, i)] = False
    for j in range(i + 1, n):
        presets[(i, j)] = False


def _preset_force_pair(
    presets: dict[tuple[int, int], bool], n: int, i: int, j: int
) -> None:
    if i > j:
        i, j = j, i
    presets[(i, j)] = True
    presets[(i, i)] = True
    presets[(j, j)] = True
    for k in range(i):
        presets[(k, j)] = False
        presets[(k, i)] = False
    for k in range(i + 1, j):
        presets[(k, j)] = False
        presets[(i, k)] = False
    for k in range(j + 1, n):
        presets[(j, k)] = False
        presets[(i, k)] = False


def _membus_kill_distinct_key_pairs(
    presets: dict[tuple[int, int], bool],
    entries: list[tuple[int, int]],
) -> int:
    """Kill ``(id_i, id_j)`` when ``entries`` lists distinct const/offset values."""
    killed = 0
    for (id_a, val_a), (id_b, val_b) in itertools.combinations(entries, 2):
        if val_a == val_b:
            continue
        assert id_a < id_b
        presets[(id_a, id_b)] = False
        killed += 1
    return killed


def _plain_exactly_one_match(literals: list[FNode]) -> FNode:
    """Exactly-one over match literals, skipping entries already fixed to false."""
    live = [lit for lit in literals if not lit.is_false()]
    if not live:
        return FALSE()
    if len(live) == 1:
        return live[0]
    forced = [lit for lit in live if lit.is_true()]
    if len(forced) > 1:
        return FALSE()
    if len(forced) == 1:
        chosen = forced[0]
        others = [Not(lit) for lit in live if lit is not chosen]
        return And(chosen, *others) if others else TRUE()
    return bool_simplify(ExactlyOne(*live))


def _parse_membus_key(key: str | None):
    return parse_membus_key(key)


def _membus_presets_from_rows(
    presets: dict[tuple[int, int], bool],
    rows: dict[int, AlignRowInfo],
    n: int,
    mult_const: list[int | None],
    *,
    log_prefix: str | None = None,
) -> None:
    prefix = f"{log_prefix} " if log_prefix else ""

    for i in range(n):
        if mult_const[i] == 0:
            _preset_force_self(presets, n, i)

    for ordn, row in rows.items():
        if ordn >= n:
            continue
        match row.local_role:
            case "input" | "output" | "inert":
                _preset_force_self(presets, n, ordn)
                logging.info(
                    "%smembus row self-match: interaction %d (%s)",
                    prefix,
                    ordn,
                    row.local_role,
                )
            case "interior":
                for p in row.local_partners:
                    if p >= n or p == ordn:
                        continue
                    i, j = (ordn, p) if ordn < p else (p, ordn)
                    _preset_force_pair(presets, n, i, j)
                    logging.info(
                        "%smembus row pair match: (%d, %d)",
                        prefix,
                        i,
                        j,
                    )

    by_const: list[tuple[int, int]] = []
    by_base: dict[str, list[tuple[int, int]]] = collections.defaultdict(list)
    for i in range(n):
        row = rows.get(i)
        if row is None or row.key is None:
            continue
        pk = row.key
        match pk.kind:
            case "const":
                if pk.const_value is not None:
                    by_const.append((i, pk.const_value))
            case "base_offset":
                assert pk.base is not None and pk.offset is not None
                by_base[pk.base].append((i, pk.offset))

    killed = _membus_kill_distinct_key_pairs(presets, by_const)
    for entries in by_base.values():
        killed += _membus_kill_distinct_key_pairs(presets, entries)

    for i in range(n):
        for j in range(i + 1, n):
            ri, rj = rows.get(i), rows.get(j)
            if (
                ri is not None
                and rj is not None
                and ri.alias_class is not None
                and rj.alias_class is not None
                and ri.alias_class != rj.alias_class
            ):
                presets[(i, j)] = False
                killed += 1

    if killed:
        logging.info("%smembus row refine: killed %d off-diagonal pairs", prefix, killed)


def _membus_match_presets(
    n: int,
    mult_const: list[int | None],
    const_args: list[tuple[int | None, ...] | None],
    p: int,
    *,
    membus_alignment: MembusAlignment | None = None,
    source_path: Path | None = None,
    log_prefix: str | None = None,
) -> dict[tuple[int, int], bool]:
    del const_args, p
    if n == 0 or membus_alignment is None or source_path is None:
        return {}

    path = source_path.resolve()
    if path == membus_alignment.before_path.resolve():
        rows = membus_alignment.before_rows
    elif path == membus_alignment.after_path.resolve():
        rows = membus_alignment.after_rows
    else:
        return {}

    presets: dict[tuple[int, int], bool] = {}
    _membus_presets_from_rows(
        presets, rows, n, mult_const, log_prefix=log_prefix
    )
    return presets


def _plain_build_match_vars(
    interactions: list,
    symbol: Callable[[int, int], FNode],
    *,
    log_prefix: str | None = None,
    source_path: Path | None = None,
    membus_alignment: MembusAlignment | None = None,
) -> dict[tuple[int, int], FNode]:
    """Build ``memory_match_i_j`` variables for all ``i <= j``, using ``FALSE`` when static."""
    p = ARGS().field_type.value
    n = len(interactions)
    mult_const, const_args = _plain_static_profile(interactions, p)
    membus_presets = _membus_match_presets(
        n,
        mult_const,
        const_args,
        p,
        membus_alignment=membus_alignment,
        source_path=source_path,
        log_prefix=log_prefix,
    )
    match_vars: dict[tuple[int, int], FNode] = {}
    static_false = 0
    membus_preset = 0
    symbols = 0

    for i in range(n):
        for j in range(i, n):
            key = (i, j)
            if i != j and _plain_pairwise_match_impossible_static(
                i, j, mult_const, const_args, p
            ):
                match_vars[key] = FALSE()
                static_false += 1
            elif key in membus_presets:
                match_vars[key] = TRUE() if membus_presets[key] else FALSE()
                membus_preset += 1
            else:
                match_vars[key] = symbol(i, j)
                symbols += 1

    prefix = f"{log_prefix} " if log_prefix else ""
    logging.info(
        "%splain_build_match_vars: %d symbols / %d static_false / %d membus_preset",
        prefix,
        symbols,
        static_false,
        membus_preset,
    )
    return match_vars


@profile
def keyed_io_relation(
    name: str,
    interactions_a: list,
    interactions_b: list,
    isi_a: list[list[FNode]],
    iso_a: list[list[FNode]],
    isi_b: list[list[FNode]],
    iso_b: list[list[FNode]],
    *,
    xmatch_name_prefix: str,
    aligned_pairs: dict[int, int] | None = None,
) -> tuple[FNode, frozenset[FNode]]:
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

    Boolean ``{xmatch_name_prefix}_xmatch_i_j`` mean: I/O row ``i`` on A is paired
    with I/O row ``j`` on B (same cell and payload). Row/column ``Iff``/``Xor``
    constraints are pure Boolean in ``xmatch`` and ``is_*``; theory only appears in
    the reification pair linking ``xmatch`` to field equalities.

    Arguments:
        name: Comment prefix for generated conjuncts (e.g. ``"INPUT RELATION"``).
        interactions_a: Interactions from the left/before encoder, same order as
            when that side's permutation check was built.
        interactions_b: Interactions from the right/after encoder.
        isi_a, iso_a: Per-interaction input/output flags on side A (lists of length ``n``).
        isi_b, iso_b: Same on side B (length ``m``).
        xmatch_name_prefix: Bus name used in ``{prefix}_xmatch_i_j`` stems.
        aligned_pairs: Optional before-index → after-index map from memory
            prealignment. When present, matching pairs become ``TRUE()``,
            conflicting pairs ``FALSE()``, and only unmapped pairs fall back to
            the ``io_and_eq`` constant-folding check.

    Returns ``(conjunction, introduced)`` where ``introduced`` are the xmatch symbols.
    """
    n, m = len(interactions_a), len(interactions_b)
    parts: list[FNode] = []

    def full_eq(i: int, j: int) -> FNode:
        """All args (key, data, timestamp) agree at indices ``i`` and ``j``."""
        return And(
            *[
                field_eq(a, b)
                for a, b in zip(interactions_a[i].args, interactions_b[j].args, strict=True)
            ]
        )

    def io_and_eq(i: int, j: int) -> FNode:
        return And(
            Iff(isi_a[i], isi_b[j]),
            Iff(iso_a[i], iso_b[j]),
            full_eq(i, j),
        )

    pairs = aligned_pairs or {}
    aligned_after = set(pairs.values())

    xmatch_vars: dict[tuple[int, int], FNode] = {}
    for i in range(n):
        mapped = pairs.get(i)
        for j in range(m):
            if j == mapped:
                xmatch_vars[(i, j)] = TRUE()
                parts.append(
                    with_comment(
                        io_and_eq(i, j),
                        f"{name}: xmatch ({i},{j}) => I/O + full eq",
                    )
                )
                continue
            if mapped is not None and j != mapped:
                xmatch_vars[(i, j)] = FALSE()
                continue
            if j in aligned_after:
                xmatch_vars[(i, j)] = FALSE()
                continue

            eq = io_and_eq(i, j)
            if eq.simplify().is_false():
                xmatch_vars[(i, j)] = FALSE()
                continue

            xmatch = Symbol(f"{xmatch_name_prefix}_xmatch_{i}_{j}", BOOL)
            xmatch_vars[(i, j)] = xmatch
            parts.append(
                with_comment(
                    Implies(xmatch, eq),
                    f"{name}: xmatch ({i},{j}) => I/O + full eq",
                )
            )

    for i in range(n):
        for j in range(m):
            if xmatch_vars[(i, j)].is_false():
                continue
            for k in range(j + 1, m):
                parts.append(
                    with_comment(
                        Not(And(xmatch_vars[(i, j)], xmatch_vars[(i, k)])),
                        f"{name}: at most one xmatch on row {i}",
                    )
                )

    for j in range(m):
        for i in range(n):
            if xmatch_vars[(i, j)].is_false():
                continue
            for k in range(i + 1, n):
                parts.append(
                    with_comment(
                        Not(And(xmatch_vars[(i, j)], xmatch_vars[(k, j)])),
                        f"{name}: at most one xmatch on column {j}",
                    )
                )

    for i in range(n):
        parts.append(
            with_comment(
                Implies(
                    Or(isi_a[i], iso_a[i]),
                    Or([xmatch_vars[(i, j)] for j in range(m)]) if m else FALSE(),
                ),
                f"{name}: row {i} I/O iff some xmatch",
            )
        )

    for j in range(m):
        parts.append(
            with_comment(
                Implies(
                    Or(isi_b[j], iso_b[j]),
                    Or([xmatch_vars[(i, j)] for i in range(n)]) if n else FALSE(),
                ),
                f"{name}: column {j} I/O iff some xmatch",
            )
        )

    parts = boolean_propagate(
        [keep_comment(p.simplify(), p) for p in parts], presimplify=False
    )

    introduced = frozenset(v for v in xmatch_vars.values() if v.is_symbol())
    return (And(*parts) if parts else TRUE(), introduced)


class TimestampCheckMixin:
    """Mixin providing axioms that enforce monotonic timestamps over bus interactions."""

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

    def ordered_permutation_check(self) -> FNode:
        """
        Encodes a permutation check for the given list of interactions. We assume
        the interactions are already well-ordered: two consecutive interactions
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
                newsym = self._symbol(
                    f"{input.symbol_name()}-{id + 1}", selects[-1].get_type().elem_type, add_prefix=False
                )
                conjuncts.append(Equals(newsym, Select(selects[-1], wrap_mod(key))))
                selects.append(newsym)
                intermediates.add(newsym)

            # fresh variable for the new value
            newval = self._symbol(f"{input.symbol_name()}-new", newsym.get_type(), add_prefix=False)
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
    
    def plain_permutation_check(
        self,
        interactions: list
    ) -> tuple[list[FNode], list[FNode], list[FNode]]:
        """Encodes a permutation check in the spirit of busat."""

        p = ARGS().field_type.value
        conjuncts = []
        n = len(interactions)
        if n == 0:
            return [], [], []
        alignment = self._cur_state.memory_bus_alignment
        skip_matches = (
            alignment is not None
            and alignment.n_before == alignment.n_after == n
            and all(alignment.before_to_after.get(i) == i for i in range(n))
        )
        if skip_matches:
            logging.info("skipping matches for %s", self.NAME)

        membus_rows = {}
        al = self._cur_state.memory_bus_alignment
        if self.NAME == "memory" and al is not None and self._cur_state.source_path is not None:
            sp = self._cur_state.source_path.resolve()
            if sp == al.before_path.resolve():
                membus_rows = al.before_rows
            elif sp == al.after_path.resolve():
                membus_rows = al.after_rows

        # Fix input/output/disabled flags from the membus role, only creating a
        # symbol for the flags a known role does not already pin to a constant.
        is_inputs, is_outputs, is_disableds = [], [], []
        for i in range(n):
            row = membus_rows.get(i)
            match row.local_role if row else None:
                case "input":
                    isin, isout, isdis = TRUE(), FALSE(), FALSE()
                case "output":
                    isin, isout, isdis = FALSE(), TRUE(), FALSE()
                case "inert":
                    isin, isout, isdis = FALSE(), FALSE(), TRUE()
                case "interior":
                    isin, isout, isdis = FALSE(), FALSE(), FALSE()
                case _:
                    isin = self._symbol(f"{self.NAME}_isinput_{i}", BOOL)
                    isout = self._symbol(f"{self.NAME}_isoutput_{i}", BOOL)
                    isdis = self._symbol(f"{self.NAME}_isdisabled_{i}", BOOL)
            is_inputs.append(isin)
            is_outputs.append(isout)
            is_disableds.append(isdis)

        mem_key_const: list[tuple[int | None, int | None]] = []
        for inter in interactions:
            addr, ptr = inter.args[0], inter.args[1]
            mem_key_const.append((
                addr.constant_value() % p if addr.is_int_constant() else None,
                ptr.constant_value() % p if ptr.is_int_constant() else None,
            ))

        def mem_keys_statically_disjoint(ii: int, jj: int) -> bool:
            ai, pi = mem_key_const[ii]
            aj, pj = mem_key_const[jj]
            if ai is not None and aj is not None and ai != aj:
                return True
            if pi is not None and pj is not None and pi != pj:
                return True
            return False


        match_vars = _plain_build_match_vars(
            interactions,
            lambda i, j: self._symbol(f"{self.NAME}_match_{i}_{j}", BOOL),
            log_prefix=self.NAME,
            source_path=self._cur_state.source_path if self.NAME == "memory" else None,
            membus_alignment=(
                self._cur_state.memory_bus_alignment
                if self.NAME == "memory"
                else None
            ),
        )

        def m(i: int, j: int) -> FNode:
            if i > j:
                i, j = j, i
            return match_vars[(i, j)]

        def mult(i: int) -> FNode:
            return interactions[i].mult

        def args(i: int) -> list[FNode]:
            return interactions[i].args

        def ts(ii: int) -> FNode:
            return args(ii)[-1]

        def is_input(i: int) -> FNode:
            return is_inputs[i]
        def is_output(i: int) -> FNode:
            return is_outputs[i]
        def is_disabled(i: int) -> FNode:
            return is_disableds[i]

        def bus_arg_constants_distinct(ii: int, jj: int, key: int) -> bool:
            a, b = args(ii)[key], args(jj)[key]
            return a.is_int_constant() and not b.is_int_constant(a.constant_value())

        def mem_key_eq(ii: int, jj: int) -> tuple[FNode, FNode]:
            return (
                field_eq(args(ii)[0], args(jj)[0]),
                field_eq(args(ii)[1], args(jj)[1]),
            )
        
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
                if m(i, j).is_false():
                    continue
                # pairwise match: mul_i + mul_j == 0 and mul_i != 0 and mul_j != 0
                conjuncts.append(
                    with_comment(
                        Implies(
                            m(i, j),
                            And(
                                field_eq(Plus(mult(i), mult(j))),
                                Not(field_eq(mult(i))),
                                Not(field_eq(mult(j)))
                            )
                        ),
                        f"match {i} and {j}: {mult(i)} + {mult(j)} == 0"
                    )
                )
                # pairwise match: data_i == data_j
                conjuncts.append(
                    with_comment(
                        Implies(
                            m(i, j),
                            And(
                                field_eq(*z) for z in zip(args(i), args(j), strict=True)
                            )
                        ),
                        f"match {i} and {j}: equal data"
                    )
                )

        # every interaction has exactly one match
        for i in range(n):
            conjuncts.append(
                with_comment(
                    _plain_exactly_one_match([m(i, j) for j in range(n)]),
                    f"interaction {i} has exactly one match"
                )
            )

        # no two inputs or two outputs have the same address space and pointer
        for i in range(n):
            if is_input(i).is_false() and is_output(i).is_false():
                continue
            for j in range(i + 1, n):
                if is_input(j).is_false() and is_output(j).is_false():
                    continue
                if mem_keys_statically_disjoint(i, j):
                    continue
                conjuncts.append(
                    with_comment(
                        Implies(
                            Or(
                                And(is_input(i), is_input(j)),
                                And(is_output(i), is_output(j)),
                            ),
                            Or(
                                Not(field_eq(args(i)[0], args(j)[0])),
                                Not(field_eq(args(i)[1], args(j)[1])),
                            )
                        ),
                        f"inputs or outputs {i} and {j} have different address spaces or pointers"
                    )
                )

        for i in range(n):
            is_actives = []
            has_inputs = []
            has_outputs = []
            for j in range(n):
                if mem_keys_statically_disjoint(i, j):
                    continue
                mke = mem_key_eq(i, j)
                if not is_disabled(j).is_true():
                    is_actives.append(And(Not(is_disabled(j)), *mke))
                if not is_input(j).is_false():
                    has_inputs.append(And(is_input(j), *mke))
                if not is_output(j).is_false():
                    has_outputs.append(And(is_output(j), *mke))
            is_active = Or(*is_actives)
            has_input = Or(*has_inputs)
            has_output = Or(*has_outputs)
            conjuncts.append(
                with_comment(
                    Implies(is_active, has_input),
                    f"key of interaction {i}: some input on that address_space/pointer",
                )
            )
            conjuncts.append(
                with_comment(
                    Implies(is_active, has_output),
                    f"key of interaction {i}: some output on that address_space/pointer",
                )
            )

        for i in range(n):
            if is_disabled(i).is_true():
                continue
            for j in range(n):
                if i == j or m(i, j).is_false():
                    continue
                if mem_keys_statically_disjoint(i, j):
                    continue
                if is_disabled(j).is_true():
                    continue
                conjuncts.append(
                    with_comment(
                        Implies(
                            And(
                                Not(is_disabled(i)),
                                Not(is_disabled(j)),
                                *mem_key_eq(i, j),
                                field_lt(ts(i), ts(j))
                            ),
                            And(Not(is_output(i)), Not(is_input(j))),
                        ),
                        f"same key {i},{j}: earlier ts not output, later ts not input",
                    )
                )

        # from hereon, the conjuncts are tuned to the actual inputs and might break on weird inputs
        # at least, they encode properties that are not immediately obvious from the specs

        if ARGS().use_memory_order:
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
                                        *mem_key_eq(i, j),
                                    ),
                                    field_eq(mult(j)),
                                ),
                                f"match {i} and {k}: index {j} between with same key => mult==0",
                            )
                        )

        # inputs and outputs have each distinct timestamps
        for i in range(n):
            if is_input(i).is_false() and is_output(i).is_false():
                continue
            for j in range(i + 1, n):
                if (is_input(i).is_false() and is_input(j).is_false()) or (is_output(i).is_false() and is_output(j).is_false()):
                    continue
                conjuncts.append(
                    with_comment(
                        Implies(
                            Or(
                                And(is_input(i), is_input(j)),
                                And(is_output(i), is_output(j)),
                            ),
                            Not(field_eq(args(i)[-1], args(j)[-1])),
                        ),
                        f"inputs or outputs {i} and {j} have different timestamps"
                    )
                )

        if ARGS().use_memory_order:
            conjuncts.extend(
                plain_memory_const_key_io_hints(
                    interactions, is_input, is_output, mult
                )
            )

        if ARGS().memory_presolve != MemoryPresolve.NONE:
            vrs = self._cur_state.bus_interaction_encoder.variable_range_checker
            coi_constraints = list(self.constraints())
            coi_constraints.extend(
                c for c in vrs.encode() if c is not None
            )

            if ARGS().memory_presolve in [MemoryPresolve.INCREMENTAL, MemoryPresolve.WITH_SAT]:
                tracked_bools = {v for v in match_vars.values() if v.is_symbol()}
                learned = plain_memory_presolve_incremental(
                    conjuncts,
                    tracked_bools,
                    coi_constraints=coi_constraints,
                    interactions=interactions,
                    match_vars=match_vars,
                )
                if learned:
                    conjuncts = learned + [c for c in conjuncts if c not in learned]

            elif ARGS().memory_presolve == MemoryPresolve.INDIVIDUAL:
                tracked_bools = {v for v in match_vars.values() if v.is_symbol()}
                learned = plain_memory_presolve_individual(
                    conjuncts,
                    tracked_bools,
                    coi_constraints=coi_constraints,
                    interactions=interactions,
                    match_vars=match_vars,
                )
                if learned:
                    conjuncts = learned + [c for c in conjuncts if c not in learned]
        simplified: list[FNode] = []
        for c in conjuncts:
            s = c.simplify()
            if not s.is_true():
                simplified.append(keep_comment(s, c))
        # ``simplified`` is already fully simplified, so skip BCP's presimplify pass.
        conjuncts = boolean_propagate(simplified, presimplify=False)
        self.plain_permutation_io = PlainPermutationIo(
            is_inputs=list(is_inputs),
            is_outputs=list(is_outputs),
            is_disableds=list(is_disableds),
            match_vars=dict(match_vars),
        )
        return (
            conjuncts,
            is_inputs,
            is_outputs,
        )

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
                                field_eq(Plus(bi.mult, bj.mult)),
                                Not(field_eq(bi.mult)),
                                Not(field_eq(bj.mult)),
                            )
                        ),
                        f"pairwise match ({i},{j}): {bi.mult} + {bj.mult} == 0"
                    )
                )

                # m_i_j => arg_k_i == arg_k_j for all args
                for arg_i, arg_j in zip(bi.args, bj.args):
                    constraints.append(
                        with_comment(
                            Implies(mv, field_eq(arg_i, arg_j)),
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
                                field_eq(bi.mult, Int(-1)),
                                field_eq(bi.mult, Int(0)),
                                field_eq(bi.mult, Int(1)),
                            )
                        ),
                        f"self-match {i}: {bi.mult} == -1, 0, 1"
                    )
                )
            else:
                constraints.append(
                    with_comment(
                        Implies(mv, field_eq(bi.mult)),
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
