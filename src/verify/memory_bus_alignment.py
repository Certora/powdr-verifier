"""Shared memory-bus alignment between before/after APC encodings.

For **array** encoding: intermediate array snapshots at matching interaction
prefix/suffix are paired and emitted as ``set-info :shared-array-*`` for
``simplify.array_subst``.

For **plain** encoding: the permutation encoding uses boolean (and int)
auxiliaries per interaction index instead of array chains; the same
prefix/suffix interaction alignment pairs those symbols analogously.
"""
import logging
from dataclasses import dataclass

from . import SetInfo
from ..simplify.skolem_utils import emit_pin_setinfo
from ..smt.conversion import SmtConverter
from ..smt.utils import FNode, Equals, BOOL
from ..utils.args import ARGS

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

SETINFO_SHARED_ARRAYS_PREFIX = ":shared-array-"


# -----------------------------------------------------------------------------
# 1. Encoding-agnostic analysis: Memory bus traces → partial alignment
# -----------------------------------------------------------------------------


def _memory_bus_id(data: dict) -> int | None:
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    for bid, btype in bus_ids.items():
        if btype == "Memory":
            return int(bid)
    return None


@dataclass(frozen=True)
class MemoryBusPartialAlignment:
    """Prefix/suffix overlap of Memory bus interaction lists (same length, same bus id)."""

    n: int
    prefix_same: int
    suffix_same: int
    shared_steps: frozenset[int]


def analyze_memory_bus_partial_alignment(
    before_data: dict, after_data: dict
) -> MemoryBusPartialAlignment | None:
    """Infer which interaction indices are structurally shared between two APC dumps."""
    mem_id = _memory_bus_id(before_data)
    if mem_id is None:
        return None

    before_mem = [
        bi for bi in before_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]
    after_mem = [
        bi for bi in after_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]

    n = len(before_mem)
    if n != len(after_mem) or n == 0:
        return None

    prefix_same = 0
    for i in range(n):
        if before_mem[i] != after_mem[i]:
            break
        prefix_same += 1

    suffix_same = 0
    for i in range(1, n + 1):
        if n - i < prefix_same:
            break
        if before_mem[-i] != after_mem[-i]:
            break
        suffix_same += 1

    shared_steps: set[int] = set()
    for i in range(prefix_same + 1):
        shared_steps.add(i)
    for i in range(n - suffix_same, n + 1):
        shared_steps.add(i)

    if not shared_steps:
        return None

    return MemoryBusPartialAlignment(n, prefix_same, suffix_same, frozenset(shared_steps))


# -----------------------------------------------------------------------------
# 2. Encoding-specific maps: before symbol → after symbol
# -----------------------------------------------------------------------------


def _array_encoding_symbol_pairs(
    alignment: MemoryBusPartialAlignment,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    before_enc = before_conv.bus_interaction_encoder.memory
    after_enc = after_conv.bus_interaction_encoder.memory

    def strip_prefix(name: str) -> str:
        for p in (BEFORE_PREFIX + "-", AFTER_PREFIX + "-"):
            if name.startswith(p):
                return name[len(p):]
        return name

    ba = before_enc.auxiliaries if hasattr(before_enc, "auxiliaries") else set()
    aa = after_enc.auxiliaries if hasattr(after_enc, "auxiliaries") else set()

    before_by_suffix: dict[str, FNode] = {}
    for s in ba:
        if s.get_type().is_array_type():
            before_by_suffix[strip_prefix(s.symbol_name())] = s

    subs: dict[FNode, FNode] = {}
    for s in aa:
        if not s.get_type().is_array_type():
            continue
        suffix = strip_prefix(s.symbol_name())
        partner = before_by_suffix.get(suffix)
        if partner is None or partner.get_type() != s.get_type():
            continue
        parts = suffix.split("-")
        if len(parts) >= 2:
            try:
                step = int(parts[1])
            except ValueError:
                continue
            if step in alignment.shared_steps:
                subs[partner] = s

    return subs


def _plain_index_pinned(i: int, n: int, prefix_same: int, suffix_same: int) -> bool:
    if i < prefix_same:
        return True
    if i >= n - suffix_same:
        return True
    return False


def _plain_pair_indices_aligned(i: int, j: int, n: int, prefix_same: int, suffix_same: int) -> bool:
    if i < prefix_same and j < prefix_same:
        return True
    if i >= n - suffix_same and j >= n - suffix_same:
        return True
    return False


def _plain_encoding_symbol_pairs(
    alignment: MemoryBusPartialAlignment,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    before_enc = before_conv.bus_interaction_encoder.memory
    nm = before_enc.NAME
    n = alignment.n
    subs: dict[FNode, FNode] = {}

    for i in range(n):
        if not _plain_index_pinned(i, n, alignment.prefix_same, alignment.suffix_same):
            continue
        for role, sort in (
            ("isinput", BOOL),
            ("isoutput", BOOL),
            ("isdisabled", BOOL),
        ):
            leaf = f"{nm}_{role}_{i}"
            b_sym = before_conv._symbol(leaf, sort)
            a_sym = after_conv._symbol(leaf, sort)
            subs[b_sym] = a_sym

    for i in range(n):
        for j in range(i, n):
            if not _plain_pair_indices_aligned(
                i, j, n, alignment.prefix_same, alignment.suffix_same
            ):
                continue
            leaf = f"{nm}_match_{i}_{j}"
            b_sym = before_conv._symbol(leaf, BOOL)
            a_sym = after_conv._symbol(leaf, BOOL)
            subs[b_sym] = a_sym

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
    reverse: bool = False,
) -> SetInfo:
    """Pair before/after memory symbols on shared prefix/suffix; emit ``set-info`` pins.

    ``subs`` maps ``{before_sym: after_sym}``.  For *completeness*
    (after-vars quantified) pass ``reverse=True`` so pins read ``Equals(after, before)``.
    For *soundness* (before-vars quantified) use ``reverse=False``.

    Encoding follows ``ARGS().memory_encoding`` (``array``, ``plain``, or empty for others).

    Pins use the ``:shared-array-*`` key prefix for historical reasons; ``array_subst``
    injects them as top-level equalities regardless of sort.
    """
    alignment = analyze_memory_bus_partial_alignment(before_data, after_data)
    if alignment is None:
        return SetInfo()
    match ARGS().memory_encoding:
        case "array":
            subs = _array_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case "plain":
            subs = _plain_encoding_symbol_pairs(alignment, before_conv, after_conv)
        case _:
            subs = {}
    logging.info(
        "memory bus pins: encoding=%r reverse=%s n=%d prefix_same=%d suffix_same=%d pair_count=%d",
        ARGS().memory_encoding,
        reverse,
        alignment.n,
        alignment.prefix_same,
        alignment.suffix_same,
        len(subs),
    )
    prefix = SETINFO_SHARED_ARRAYS_PREFIX[1:]
    if reverse:
        pins = [Equals(v, k) for k, v in subs.items()]
    else:
        pins = [Equals(k, v) for k, v in subs.items()]
    cmds = [emit_pin_setinfo(prefix, i, eq) for i, eq in enumerate(pins)]
    return SetInfo(cmds)
