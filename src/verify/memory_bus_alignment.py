"""Memory-bus symbol pins between before/after APC encodings."""
from __future__ import annotations

import logging

from . import SetInfos, SkolemPin, SkolemPinKind
from ..smt.conversion import SmtConverter
from ..smt.utils import *
from ..utils.stats import stats_dump
from ..utils.args import ARGS
from .membus_types import MembusAlignment

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

_LOG = logging.getLogger(__name__)


def _array_encoding_symbol_pairs(
    alignment: MembusAlignment,
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
    alignment: MembusAlignment,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    before_io = before_conv.bus_interaction_encoder.memory.plain_permutation_io
    after_io = after_conv.bus_interaction_encoder.memory.plain_permutation_io
    if before_io is None or after_io is None:
        raise RuntimeError(
            "plain_permutation_io missing: plain memory encoding did not run on both sides"
        )
    m = alignment.before_to_after
    nm = before_conv.bus_interaction_encoder.memory.NAME
    subs: dict[FNode, FNode] = {}

    for i_b, i_a in m.items():
        subs[Symbol(f"{nm}_xmatch_{i_b}_{i_a}", BOOL)] = TRUE()

        subs[before_io.is_inputs[i_b]] = after_io.is_inputs[i_a]
        subs[before_io.is_outputs[i_b]] = after_io.is_outputs[i_a]
        subs[before_io.is_disableds[i_b]] = after_io.is_disableds[i_a]
        for j_b, j_a in m.items():
            if i_b > j_b:
                continue
            subs[before_io.match_vars[(i_b, j_b)]] = after_io.match_vars[(i_a, j_a)]

    return subs


def emit_memory_equalities(
    alignment: MembusAlignment | None,
    before_conv: SmtConverter,
    after_conv: SmtConverter,
    *,
    reverse: bool = False,
) -> SetInfos:
    if alignment is None:
        _LOG.info("memory bus pins skipped (no alignment)")
        stats_dump("memory-bus-pins", {"pin_count": 0, "skipped": True, "reason": "no_alignment"})
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
    stats_dump(
        "memory-bus-pins",
        {
            "encoding": ARGS().memory_encoding,
            "reverse": reverse,
            "n_before": alignment.n_before,
            "n_after": alignment.n_after,
            "aligned_steps": len(alignment.before_to_after),
            "pin_count": len(pins),
        },
    )
    return SetInfos(
        equations=[SkolemPin(p, SkolemPinKind.MEMORY_BUS) for p in pins],
    )
