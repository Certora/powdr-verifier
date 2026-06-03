"""Shared memory-bus alignment between before/after APC encodings.

Aligned before/after symbols (array snapshots or plain ``memory_match_*``)
are emitted as ``set-info :skolem-derived-*`` so ``simplify.skolem_derived``
pins quantified sides to free witnesses (then ``lift_forall`` hoists).
"""
from __future__ import annotations

import logging
import time
from collections.abc import Iterable, Iterator
from itertools import product
from dataclasses import dataclass

from pathlib import Path

from . import SetInfo
from ..bus_interactions.single_interaction_encoder import BusInteraction
from ..report.action import Action
from ..smt.conversion import SmtConverter
from ..smt.utils import *
from ..utils.args import ARGS

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

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


def _flatten_outer_conjunctions(formulas: Iterable[FNode]) -> Iterator[FNode]:
    for formula in formulas:
        if formula.is_and():
            yield from _flatten_outer_conjunctions(formula.args())
        else:
            yield formula


def _flat_memory_encoder_row(row: BusInteraction) -> tuple[FNode, list[FNode]]:
    mult, rest = row.mult, row.args
    a, p, data, ts = rest
    return mult, [a, p, *data, ts]


def _strip_prefix(row: BusInteraction, prefix: str) -> BusInteraction:
    return BusInteraction(
        strip_prefix_from_vars(row.mult, prefix),
        tuple(strip_prefix_from_vars(a, prefix) for a in row.args),
    )


_MEMORY_ALIGN_CHECK_TACTIC_FULL = (
    "z3-propagate-values:bounds:rewrite:gxor:mod_inv:demod"
)
_MEMORY_ALIGN_CHECK_TACTIC_BARE = "z3-propagate-values:demod"


def _encode_equiv_formula(row_b: BusInteraction, row_a: BusInteraction) -> FNode | None:
    mb, flat_b = _flat_memory_encoder_row(row_b)
    ma, flat_a = _flat_memory_encoder_row(row_a)
    assert len(flat_b) == len(flat_a)
    return And(field_eq(mb, ma), *[field_eq(x, y) for x, y in zip(flat_b, flat_a)])


def _check_is_valid(
    formula: FNode,
    *,
    smt_dump_base: Path | None,
    tactic: str = _MEMORY_ALIGN_CHECK_TACTIC_FULL,
) -> bool | None:
    return simplify_and_check(
        formula,
        simplify_timeout=1.0,
        check_timeout=1.0,
        tactic=tactic,
        smt_dump_base=smt_dump_base,
    )


def _check_equivalent_bare(
    row_b: BusInteraction,
    row_a: BusInteraction,
    *,
    smt_dump_base: Path | None,
) -> bool | None:
    """Encoder equality: trivial ``simplify`` to true, else bare SMT check. ``True``/``False``/unknown ``None``."""
    eq = _encode_equiv_formula(row_b, row_a).simplify()
    if eq.is_true():
        return True
    elif eq.is_false():
        return False

    if _check_is_valid(
        eq,
        smt_dump_base=smt_dump_base,
        tactic=_MEMORY_ALIGN_CHECK_TACTIC_BARE,
    ):
        return True
    return None


def _check_equivalent_contextual(
    row_b: BusInteraction,
    row_a: BusInteraction,
    before_constraints: Iterable[FNode],
    after_constraints: Iterable[FNode],
    *,
    smt_dump_base: Path | None,
) -> bool | None:
    """SMT with APC context; rows and constraints use matching stripped symbol names."""
    eq = _encode_equiv_formula(row_b, row_a).simplify()
    assert not eq.is_true()
    
    syms = frozenset(eq.get_free_variables())
    if False:
        rel = _constraints_referencing(before_constraints, syms) + _constraints_referencing(
            after_constraints, syms
        )
    else:
        # do not do relevance check
        rel = before_constraints + after_constraints
    if not rel:
        _LOG.debug(
            "memory align no relevant constraints for interaction vars free_sym_count=%d",
            len(syms),
        )
        return None
    return _check_is_valid(Implies(And(*rel), eq), smt_dump_base=smt_dump_base)


def uniq(
    pairs: Iterable,
) -> Iterator:
    seen: set = set()
    for p in pairs:
        if p not in seen:
            seen.add(p)
            yield p


def _iter_memory_alignment_index_pairs_core(
    before_indices: Iterable[int],
    after_indices: Iterable[int],
) -> Iterator[tuple[int, int]]:
    bk = list(before_indices)
    ak = list(after_indices)
    yield from zip(bk, ak)
    yield from zip(reversed(bk), reversed(ak))
    for b,a in product(bk, ak):
        if b % 2 != a % 2:
            continue
        yield b, a


def analyze_memory_bus_partial_alignment(
    before_data: dict,
    after_data: dict,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
    *,
    before_constraints: Iterable[FNode],
    after_constraints: Iterable[FNode],
    parent_action: Action,
    smt_dump_base: Path | None = None,
) -> MemoryBusPartialAlignment | None:
    """Infer aligned Memory interaction indices.

    Walks matching diagonal prefix and tail; each pair tries dump JSON equality before SMT.
    """
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
        bi for bi in before_data["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    before_mem = { idx: bi for idx, bi in enumerate(before_mem) }
    after_mem = [
        bi for bi in after_data["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    after_mem = { idx: bi for idx, bi in enumerate(after_mem) }


    _LOG.debug(f"memory bus alignment: before_mem={before_mem} after_mem={after_mem}")
    nb, na = len(before_mem), len(after_mem)
    if nb == 0 or na == 0:
        return None

    bc_strip = tuple(
        strip_prefix_from_vars(c, f"{BEFORE_PREFIX}-")
        for c in _flatten_outer_conjunctions(before_constraints)
    )
    ac_strip = tuple(
        strip_prefix_from_vars(c, f"{AFTER_PREFIX}-")
        for c in _flatten_outer_conjunctions(after_constraints)
    )

    before_to_after: dict[int, int] = {}
    counters = {
        "syntax-checks": 0,
        "syntax-matches": 0,
        "syntax-time": 0,
        "bare-checks": 0,
        "bare-true": 0,
        "bare-false": 0,
        "bare-unknown": 0,
        "bare-time": 0,
        "context-checks": 0,
        "context-true": 0,
        "context-false": 0,
        "context-unknown": 0,
        "context-time": 0,
    }

    bk0, ak0 = list(before_mem.keys()), list(after_mem.keys())
    t0 = time.perf_counter()
    for kb, ka in _iter_memory_alignment_index_pairs_core(bk0, ak0):
        if kb not in before_mem or ka not in after_mem:
            continue
        counters["syntax-checks"] += 1
        if before_mem[kb] == after_mem[ka]:
            counters["syntax-matches"] += 1
            _LOG.debug(f"memory bus alignment: syntactic match {kb} -> {ka}")
            before_to_after[kb] = ka
            del before_mem[kb]
            del after_mem[ka]
    counters["syntax-time"] = time.perf_counter() - t0

    bk0 = list(before_mem.keys())
    ak0 = list(after_mem.keys())
    before_mem = {
        idx: _strip_prefix(
            before_conv.bus_interaction_encoder.memory._interactions[idx],
            f"{BEFORE_PREFIX}-",
        )
        for idx in bk0
    }
    after_mem = {
        idx: _strip_prefix(
            after_conv.bus_interaction_encoder.memory._interactions[idx],
            f"{AFTER_PREFIX}-",
        )
        for idx in ak0
    }

    excluded = set()

    t0 = time.perf_counter()
    for kb, ka in uniq(_iter_memory_alignment_index_pairs_core(bk0, ak0)):
        if kb not in before_mem or ka not in after_mem:
            continue
        match _check_equivalent_bare(before_mem[kb], after_mem[ka], smt_dump_base=smt_dump_base):
            case True:
                counters["bare-true"] += 1
                _LOG.debug("memory bus alignment: bare match %s -> %s", kb, ka)
                before_to_after[kb] = ka
                del before_mem[kb]
                del after_mem[ka]
            case False:
                counters["bare-false"] += 1
                _LOG.debug("memory bus alignment: bare mismatch %s -> %s", kb, ka)
                excluded.add((kb, ka))
            case None:
                counters["bare-unknown"] += 1
    counters["bare-time"] = time.perf_counter() - t0

    t0 = time.perf_counter()
    for kb, ka in uniq(_iter_memory_alignment_index_pairs_core(bk0, ak0)):
        if kb not in before_mem or ka not in after_mem or (kb, ka) in excluded:
            continue
        row_b, row_a = before_mem[kb], after_mem[ka]
        match _check_equivalent_contextual(
            row_b,
            row_a,
            bc_strip,
            ac_strip,
            smt_dump_base=smt_dump_base,
        ):
            case True:
                counters["context-true"] += 1
                _LOG.debug("memory bus alignment: contextual match %s -> %s", kb, ka)
                before_to_after[kb] = ka
                del before_mem[kb]
                del after_mem[ka]
            case False:
                counters["context-false"] += 1
            case None:
                counters["context-unknown"] += 1
    counters["context-time"] = time.perf_counter() - t0

    parent_action += counters

    pair_preview = before_to_after if len(before_to_after) <= 16 else {
        **dict(list(before_to_after.items())[:12]),
        "_truncated": len(before_to_after),
    }
    _LOG.info(
        "memory bus alignment: n_before=%d n_after=%d aligned_pairs=%d pairs=%s",
        nb,
        na,
        len(before_to_after),
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
    parent_action: Action,
    reverse: bool = False,
    smt_dump_base: Path | None = None,
) -> SetInfo:
    """Pair before/after memory symbols on shared prefix/suffix; record pin equations.

    ``subs`` maps ``{before_sym: after_sym}``.  For *completeness*
    (after-vars quantified) pass ``reverse=True`` so pins read ``Equals(after, before)``.
    For *soundness* (before-vars quantified) use ``reverse=False``.

    Encoding follows ``ARGS().memory_encoding`` (``array``, ``plain``, ``none``, or empty for others).

    ``before_constraints`` / ``after_constraints`` are passed from the verifier:
    derived-column and elimination ``Equals`` terms (stripped for contextual SMT).

    Equations are serialized as ``:skolem-derived-*`` set-info when building the
    script (see :class:`SetInfo`).
    """
    with parent_action.action("memory-bus-alignment") as align_a:
        align_a += {"file": smt_dump_base.name}
        align_a += {"reverse": reverse}
        alignment = analyze_memory_bus_partial_alignment(
            before_data,
            after_data,
            before_conv,
            after_conv,
            before_constraints=before_constraints,
            after_constraints=after_constraints,
            parent_action=align_a,
            smt_dump_base=smt_dump_base,
        )
    if alignment is None:
        _LOG.info("memory bus pins skipped (no alignment)")
        return SetInfo()
    match ARGS().memory_encoding:
        case "array":
            subs = _array_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case "plain":
            subs = _plain_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case "none":
            subs = {}
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
    if reverse:
        pins = [Equals(v, k) for k, v in subs.items()]
    else:
        pins = [Equals(k, v) for k, v in subs.items()]
    return SetInfo(equations=pins)
