"""Shared memory-bus alignment between before/after APC encodings.

Aligned before/after symbols (array snapshots or plain ``memory_match_*``)
are emitted as ``set-info :skolem-memory-bus-*`` keys so ``simplify.skolem_derived``
pins quantified sides to free witnesses (then ``lift_forall`` hoists).
"""
from __future__ import annotations

import logging
import time
from collections.abc import Iterable, Iterator
from itertools import product
from dataclasses import dataclass

from pathlib import Path

from . import SetInfos, SkolemPin, SkolemPinKind
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

    ``before_to_after`` maps aligned before interaction indices to after indices.
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
    "z3-propagate-values:bounds:rewrite:bitwise:mod_inv:demod"
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


def analyze_memory_bus_partial_alignment_legacy(
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
    """Infer aligned Memory interaction indices (pair enumeration).

    Walks matching diagonal prefix and tail; each pair tries dump JSON equality before SMT.
    """
    mem_id = _memory_bus_id(before_data)
    assert mem_id is not None
    assert _memory_bus_id(after_data) == mem_id

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
    assert nb >= na

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
        "syntax-matches": 0,
        "bare-true": 0,
        "bare-false": 0,
        "bare-unknown": 0,
        "bare-time": 0,
        "context-true": 0,
        "context-false": 0,
        "context-unknown": 0,
        "context-time": 0,
    }

    bk0, ak0 = list(before_mem.keys()), list(after_mem.keys())
    for kb, ka in _iter_memory_alignment_index_pairs_core(bk0, ak0):
        if kb not in before_mem or ka not in after_mem:
            continue
        if before_mem[kb] == after_mem[ka]:
            counters["syntax-matches"] += 1
            _LOG.debug(f"memory bus alignment: syntactic match {kb} -> {ka}")
            before_to_after[kb] = ka
            del before_mem[kb]
            del after_mem[ka]

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
    """Infer aligned Memory indices (monotone subsequence: no reorder, no insertions).

    Same-length traces use ``i -> i``. Otherwise sweeps only window pairs
    ``|i-j| <= n_before - n_after`` with singleton propagation between passes.
    """
    mem_id = _memory_bus_id(before_data)
    assert mem_id is not None
    assert _memory_bus_id(after_data) == mem_id

    before_list = [
        bi for bi in before_data["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    after_list = [
        bi for bi in after_data["machine"]["bus_interactions"] if bi["id"] == mem_id
    ]
    nb, na = len(before_list), len(after_list)
    if nb == 0 or na == 0:
        return None
    assert nb >= na

    if nb == na:
        m = {i: i for i in range(nb)}
        parent_action += {
            "identity-shortcut": True,
        }
        _LOG.info(
            "memory bus alignment (identity): n_before=%d n_after=%d aligned_pairs=%d",
            nb,
            na,
            nb,
        )
        return MemoryBusPartialAlignment(nb, na, m)

    bc_strip = tuple(
        strip_prefix_from_vars(c, f"{BEFORE_PREFIX}-")
        for c in _flatten_outer_conjunctions(before_constraints)
    )
    ac_strip = tuple(
        strip_prefix_from_vars(c, f"{AFTER_PREFIX}-")
        for c in _flatten_outer_conjunctions(after_constraints)
    )

    counters = {
        "syntax-matches": 0,
        "singleton-matches": 0,
        "bare-true": 0,
        "bare-false": 0,
        "bare-unknown": 0,
        "bare-time": 0.0,
        "context-true": 0,
        "context-false": 0,
        "context-unknown": 0,
        "context-time": 0.0,
    }

    before_json = {i: before_list[i] for i in range(nb)}
    after_json = {j: after_list[j] for j in range(na)}
    before_to_after: dict[int, int] = {}
    D = nb - na

    def feasible_after(b: int) -> list[int]:
        lo_w = max(0, b - D)
        hi_w = min(na - 1, b)
        for bb in range(b - 1, -1, -1):
            if bb in before_to_after:
                lo_w = max(lo_w, before_to_after[bb] + 1)
                break
        for bb in range(b + 1, nb):
            if bb in before_to_after:
                hi_w = min(hi_w, before_to_after[bb] - 1)
                break
        used_a = set(before_to_after.values())
        return [a for a in range(lo_w, hi_w + 1) if a not in used_a]

    def syntax_sweep() -> None:
        for b in range(nb):
            if b in before_to_after:
                continue
            for a in feasible_after(b):
                if before_json[b] == after_json[a]:
                    before_to_after[b] = a
                    counters["syntax-matches"] += 1
                    break

    def singleton_sweep() -> None:
        for b in range(nb):
            if b in before_to_after:
                continue
            if b == 0 and 1 in before_to_after and before_to_after[1] == 1:
                before_to_after[0] = 0
                counters["singleton-matches"] += 1
                continue
            if b == nb-1 and nb-2 in before_to_after and before_to_after[nb-2] == na-2:
                before_to_after[nb-1] = na-1
                counters["singleton-matches"] += 1
                continue
            if b == 0 or b == nb - 1:
                continue
            if b-1 in before_to_after and b+1 in before_to_after and before_to_after[b-1] + 2 == before_to_after[b+1]:
                before_to_after[b] = before_to_after[b-1] + 1
                counters["singleton-matches"] += 1

    syntax_sweep()
    singleton_sweep()

    used_after = set(before_to_after.values())
    bk0 = sorted(b for b in range(nb) if b not in before_to_after)
    ak0 = sorted(a for a in range(na) if a not in used_after)
    before_rows: dict[int, BusInteraction] = {
        idx: _strip_prefix(
            before_conv.bus_interaction_encoder.memory._interactions[idx],
            f"{BEFORE_PREFIX}-",
        )
        for idx in bk0
    }
    after_rows: dict[int, BusInteraction] = {
        idx: _strip_prefix(
            after_conv.bus_interaction_encoder.memory._interactions[idx],
            f"{AFTER_PREFIX}-",
        )
        for idx in ak0
    }
    excluded: set[tuple[int, int]] = set()

    def bare_sweep() -> None:
        t0 = time.perf_counter()
        for b in range(nb):
            if b in before_to_after:
                continue
            for a in feasible_after(b):
                match _check_equivalent_bare(
                    before_rows[b], after_rows[a], smt_dump_base=smt_dump_base
                ):
                    case True:
                        counters["bare-true"] += 1
                        _LOG.debug("memory bus alignment: bare match %s -> %s", b, a)
                        before_to_after[b] = a
                        break
                    case False:
                        counters["bare-false"] += 1
                        _LOG.debug("memory bus alignment: bare mismatch %s -> %s", b, a)
                        excluded.add((b, a))
                    case None:
                        counters["bare-unknown"] += 1
        counters["bare-time"] += time.perf_counter() - t0

    def context_sweep() -> None:
        t0 = time.perf_counter()
        for b in range(nb):
            if b in before_to_after:
                continue
            for a in feasible_after(b):
                if (b, a) in excluded:
                    continue
                match _check_equivalent_contextual(
                    before_rows[b], after_rows[a],
                    bc_strip,
                    ac_strip,
                    smt_dump_base=smt_dump_base,
                ):
                    case True:
                        counters["context-true"] += 1
                        before_to_after[b] = a
                        break
                    case False:
                        counters["context-false"] += 1
                    case None:
                        counters["context-unknown"] += 1
        counters["context-time"] += time.perf_counter() - t0

    bare_sweep()
    singleton_sweep()
    context_sweep()
    singleton_sweep()

    parent_action += counters

    _LOG.info(
        "memory bus alignment: n_before=%d n_after=%d aligned_pairs=%d",
        nb,
        na,
        len(before_to_after),
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
    """Pair ``memory_match_{i}_{j}`` for aligned indices via ``before_to_after``."""
    m = alignment.before_to_after
    nm = before_conv.bus_interaction_encoder.memory.NAME
    subs: dict[FNode, FNode] = {}
    def add_sub(b, a):
        subs[before_conv._symbol(b, BOOL)] = after_conv._symbol(a, BOOL)

    for i_b, i_a in m.items():
        add_sub(f"{nm}_isinput_{i_b}", f"{nm}_isinput_{i_a}")
        add_sub(f"{nm}_isoutput_{i_b}", f"{nm}_isoutput_{i_a}")
        add_sub(f"{nm}_isdisabled_{i_b}", f"{nm}_isdisabled_{i_a}")

        for j_b, j_a in m.items():
            if i_b > j_b:
                continue
            add_sub(f"{nm}_match_{i_b}_{j_b}", f"{nm}_match_{i_a}_{j_a}")

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
) -> SetInfos:
    """Pair before/after memory symbols using alignment; record pin equations.

    ``subs`` maps ``{before_sym: after_sym}``.  For *completeness*
    (after-vars quantified) pass ``reverse=True`` so pins read ``Equals(after, before)``.
    For *soundness* (before-vars quantified) use ``reverse=False``.

    Encoding follows ``ARGS().memory_encoding`` (``array``, ``plain``, ``none``, or empty for others).

    ``before_constraints`` / ``after_constraints`` are passed from the verifier:
    derived-column and substitution ``Equals`` terms (stripped for contextual SMT).

    Equations are serialized as ``:skolem-memory-bus-*`` set-info when building the
    script (see :class:`SetInfos`).
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
        return SetInfos()
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
    return SetInfos(
        equations=[SkolemPin(p, SkolemPinKind.MEMORY_BUS) for p in pins],
    )
