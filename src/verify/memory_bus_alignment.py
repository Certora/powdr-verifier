"""Shared memory-bus alignment between before/after APC encodings.

For **array** encoding: intermediate array snapshots at matching interaction
prefix/suffix are paired and emitted as ``set-info :shared-array-*`` for
``simplify.array_subst``.

For **plain** encoding: the permutation encoding uses boolean (and int)
auxiliaries per interaction index instead of array chains; the same
prefix/suffix interaction alignment pairs those symbols analogously.
"""
from __future__ import annotations

import logging
from collections.abc import Iterable
from dataclasses import dataclass

from pysmt.exceptions import SolverReturnedUnknownResultError

from . import SetInfo
from ..bus_interactions.single_interaction_encoder import BusInteraction
from ..simplify.skolem_utils import emit_pin_setinfo
from ..smt.conversion import SmtConverter
from ..smt.utils import *
from ..utils.args import ARGS

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

SETINFO_SHARED_ARRAYS_PREFIX = ":shared-array-"

_LOG = logging.getLogger(__name__)


# -----------------------------------------------------------------------------
# 1. Encoding-agnostic analysis: Memory bus traces → partial alignment
# -----------------------------------------------------------------------------


def _memory_bus_id(data: dict) -> int | None:
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    for bid, btype in bus_ids.items():
        if btype == "Memory":
            return int(bid)
    return None



@dataclass
class MemoryBusPartialAlignment:
    """Structural overlap of Memory interaction lists (lengths may differ).

    ``before_to_after`` maps aligned before interaction indices to after indices
    (prefix at equal indices, then matching tails without re-entering the strict-prefix band).
    """

    n_before: int
    n_after: int
    before_to_after: dict[int, int]


def _constraints_referencing(
    constraints: Iterable[FNode], symbols: frozenset[FNode]
) -> list[FNode]:
    return [c for c in constraints if c.get_free_variables() & symbols]


def _flat_memory_encoder_row(row: BusInteraction) -> tuple[FNode, list[FNode]]:
    mult, rest = row.mult, row.args
    a, p, data, ts = rest
    return mult, [a, p, *data, ts]


def _memory_encoder_interaction_equiv_formula(row_b: BusInteraction, row_a: BusInteraction) -> FNode | None:
    mb, flat_b = _flat_memory_encoder_row(row_b)
    ma, flat_a = _flat_memory_encoder_row(row_a)
    if len(flat_b) != len(flat_a):
        return None
    return And(Equals(mb, ma), *[Equals(x, y) for x, y in zip(flat_b, flat_a)])


def _memory_interaction_indices_equivalent(
    before_conv: SmtConverter,
    after_conv: SmtConverter,
    ib: int,
    ia: int,
    before_constraints: Iterable[FNode],
    after_constraints: Iterable[FNode],
) -> bool:
    row_b = before_conv.bus_interaction_encoder.memory._interactions[ib]
    row_a = after_conv.bus_interaction_encoder.memory._interactions[ia]
    eq_raw = _memory_encoder_interaction_equiv_formula(row_b, row_a)
    if eq_raw is None:
        _LOG.debug(
            "memory align SMT shape mismatch before_idx=%d after_idx=%d (flat arg lengths differ)",
            ib,
            ia,
        )
        return False
    eq = eq_raw.simplify()
    if eq.is_true():
        _LOG.debug(
            "memory align trivial SMT equality before_idx=%d after_idx=%d",
            ib,
            ia,
        )
        return True

    opts = {"rlimit": 100000}
    name = ARGS().solver

    def try_valid(formula: FNode) -> bool | None:
        with Solver(logic=QF_UFNIA, name=name, solver_options=opts) as s:
            try:
                return bool(s.is_valid(formula))
            except SolverReturnedUnknownResultError:
                return None

    r0 = try_valid(eq)
    if r0 is True:
        _LOG.debug(
            "memory align SMT valid without context before_idx=%d after_idx=%d solver=%r",
            ib,
            ia,
            name,
        )
        return True
    if r0 is None:
        _LOG.debug(
            "memory align SMT unknown (bare) before_idx=%d after_idx=%d solver=%r",
            ib,
            ia,
            name,
        )

    syms = frozenset(eq.get_free_variables())
    rel = _constraints_referencing(before_constraints, syms) + _constraints_referencing(
        after_constraints, syms
    )
    if not rel:
        _LOG.debug(
            "memory align no relevant constraints for interaction vars before_idx=%d "
            "after_idx=%d (bare_valid=%s) free_sym_count=%d",
            ib,
            ia,
            r0,
            len(syms),
        )
        return False
    r1 = try_valid(Implies(And(*rel), eq))
    if r1 is True:
        _LOG.debug(
            "memory align SMT valid with %d constraint(s) before_idx=%d after_idx=%d",
            len(rel),
            ib,
            ia,
        )
        return True
    _LOG.debug(
        "memory align SMT not proved before_idx=%d after_idx=%d bare=%s contextual=%s "
        "relevant_constraints=%d",
        ib,
        ia,
        r0,
        r1,
        len(rel),
    )
    return False


def analyze_memory_bus_partial_alignment(
    before_data: dict,
    after_data: dict,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
    *,
    before_constraints: Iterable[FNode],
    after_constraints: Iterable[FNode],
) -> MemoryBusPartialAlignment | None:
    """Infer aligned Memory interaction indices; JSON equality first, else SMT equivalence."""
    mem_id = _memory_bus_id(before_data)
    if mem_id is None or _memory_bus_id(after_data) != mem_id:
        _LOG.debug(
            "memory bus alignment skipped: Memory bus id missing or differs between dumps "
            "(before=%s after=%s)",
            mem_id,
            _memory_bus_id(after_data),
        )
        return None

    before_mem = [
        bi for bi in before_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]
    after_mem = [
        bi for bi in after_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]

    nb, na = len(before_mem), len(after_mem)
    if nb == 0 or na == 0:
        _LOG.info(
            "memory bus alignment skipped: empty Memory interaction list (bus_id=%s "
            "n_before=%d n_after=%d)",
            mem_id,
            nb,
            na,
        )
        return None

    bc = tuple(before_constraints)
    ac = tuple(after_constraints)

    json_eq = 0
    smt_ok = 0
    smt_fail = 0

    def eqv(ib: int, ia: int) -> bool:
        nonlocal json_eq, smt_ok, smt_fail
        if before_mem[ib] == after_mem[ia]:
            json_eq += 1
            return True
        ok = _memory_interaction_indices_equivalent(
            before_conv, after_conv, ib, ia, bc, ac
        )
        if ok:
            smt_ok += 1
        else:
            smt_fail += 1
        return ok

    before_to_after: dict[int, int] = {}
    i = 0
    while i < min(nb, na) and eqv(i, i):
        before_to_after[i] = i
        i += 1
    t = 0
    while t < min(nb, na):
        ib = nb - 1 - t
        ia = na - 1 - t
        if ib < i or ia < i:
            break
        if not eqv(ib, ia):
            break
        before_to_after[ib] = ia
        t += 1

    if not before_to_after:
        _LOG.info(
            "memory bus alignment: no aligned pairs (bus_id=%s n_before=%d n_after=%d)",
            mem_id,
            nb,
            na,
        )
        return None

    pair_preview = before_to_after if len(before_to_after) <= 16 else {
        **dict(list(before_to_after.items())[:12]),
        "_truncated": len(before_to_after),
    }
    _LOG.info(
        "memory bus alignment: bus_id=%s n_before=%d n_after=%d aligned_pairs=%d "
        "pair_checks_json=%d pair_checks_smt_ok=%d pair_checks_smt_fail=%d "
        "constraint_pool_before=%d after=%d pairs=%s",
        mem_id,
        nb,
        na,
        len(before_to_after),
        json_eq,
        smt_ok,
        smt_fail,
        len(bc),
        len(ac),
        pair_preview,
    )

    return MemoryBusPartialAlignment(nb, na, before_to_after)


# -----------------------------------------------------------------------------
# 2. Encoding-specific maps: before symbol → after symbol
# -----------------------------------------------------------------------------


def _array_encoding_symbol_pairs(
    alignment: MemoryBusPartialAlignment,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    before_enc = before_conv.bus_interaction_encoder.memory
    nm = before_enc.NAME
    m = alignment.before_to_after

    def strip_prefix(name: str) -> str:
        for p in (BEFORE_PREFIX + "-", AFTER_PREFIX + "-"):
            if name.startswith(p):
                return name[len(p):]
        return name

    ba = before_enc.auxiliaries if hasattr(before_enc, "auxiliaries") else set()
    subs: dict[FNode, FNode] = {}

    for s in ba:
        if not s.get_type().is_array_type():
            continue
        sn = strip_prefix(s.symbol_name())
        parts = sn.split("-", 2)
        if len(parts) < 3 or parts[0] != nm:
            continue
        try:
            i_b = int(parts[1])
        except ValueError:
            continue
        i_a = m.get(i_b)
        if i_a is None:
            continue
        rest = parts[2]
        subs[s] = after_conv._symbol(f"{nm}-{i_a}-{rest}", s.get_type())

    return subs


def _plain_encoding_symbol_pairs(
    alignment: MemoryBusPartialAlignment,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    """Pair ``memory_match_{i}_{j}`` across sides for aligned interaction pairs.

    Uses ``alignment.before_to_after``: maximal initial run with ``m[k] == k`` as the
    shared-prefix before-indices, then tail pairs ``(nb-1-t, na-1-t)`` with ``m[ib]==ia``
    outside that prefix band on both sides.
    """
    m = alignment.before_to_after
    nb, na = alignment.n_before, alignment.n_after
    nm = before_conv.bus_interaction_encoder.memory.NAME

    prefix_before: set[int] = set()
    k = 0
    while k < min(nb, na) and m.get(k) == k:
        prefix_before.add(k)
        k += 1
    pfx_excl_end = k

    suffix_before: set[int] = set()
    t = 0
    while t < min(nb, na):
        ib, ia = nb - 1 - t, na - 1 - t
        if ib < pfx_excl_end or ia < pfx_excl_end:
            break
        if m.get(ib) != ia:
            break
        suffix_before.add(ib)
        t += 1

    subs: dict[FNode, FNode] = {}
    for i_b in range(nb):
        for j_b in range(i_b, nb):
            if i_b not in m or j_b not in m:
                continue
            i_a, j_a = m[i_b], m[j_b]
            in_prefix = i_b in prefix_before and j_b in prefix_before
            in_suffix = i_b in suffix_before and j_b in suffix_before
            if not (in_prefix or in_suffix):
                continue
            b_leaf = f"{nm}_match_{i_b}_{j_b}"
            a_leaf = f"{nm}_match_{i_a}_{j_a}"
            subs[before_conv._symbol(b_leaf, BOOL)] = after_conv._symbol(a_leaf, BOOL)

    return subs


# -----------------------------------------------------------------------------
# 3. Public entry: alignment + encoding dispatch + set-info pins
# -----------------------------------------------------------------------------


def emit_memory_equalities(
    before_data: dict,
    after_data: dict,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
    *,
    before_constraints: Iterable[FNode],
    after_constraints: Iterable[FNode],
    reverse: bool = False,
) -> SetInfo:
    """Pair before/after memory symbols on shared prefix/suffix; emit ``set-info`` pins.

    ``subs`` maps ``{before_sym: after_sym}``.  For *completeness*
    (after-vars quantified) pass ``reverse=True`` so pins read ``Equals(after, before)``.
    For *soundness* (before-vars quantified) use ``reverse=False``.

    Encoding follows ``ARGS().memory_encoding`` (``array``, ``plain``, or empty for others).

    ``before_constraints`` / ``after_constraints`` (typically APC ``constraints``)
    refine SMT equivalence when JSON differs from trivial inequality.

    Pins use the ``:shared-array-*`` key prefix for historical reasons; ``array_subst``
    injects them as top-level equalities regardless of sort.
    """
    alignment = analyze_memory_bus_partial_alignment(
        before_data,
        after_data,
        before_conv,
        after_conv,
        before_constraints=before_constraints,
        after_constraints=after_constraints,
    )
    if alignment is None:
        _LOG.info("memory bus pins skipped (no alignment)")
        return SetInfo()
    match ARGS().memory_encoding:
        case "array":
            subs = _array_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case "plain":
            subs = _plain_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case _:
            subs = {}
    logging.info(
        "memory bus pins: encoding=%r reverse=%s n_before=%d n_after=%d "
        "aligned_steps=%d pair_count=%d",
        ARGS().memory_encoding,
        reverse,
        alignment.n_before,
        alignment.n_after,
        len(alignment.before_to_after),
        len(subs),
    )
    prefix = SETINFO_SHARED_ARRAYS_PREFIX[1:]
    if reverse:
        pins = [Equals(v, k) for k, v in subs.items()]
    else:
        pins = [Equals(k, v) for k, v in subs.items()]
    cmds = [emit_pin_setinfo(prefix, i, eq) for i, eq in enumerate(pins)]
    return SetInfo(cmds)
