from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

from ..utils.args import ARGS

if TYPE_CHECKING:
    from .memory_bus_alignment import MemoryBusPartialAlignment

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class VerifyPreanalysis:
    memory_bus_alignment: MemoryBusPartialAlignment | None = None


DEFAULT_VERIFY_PREANALYSIS = VerifyPreanalysis()


def analyze_verify_preanalysis(
    before: dict[str, Any], after: dict[str, Any]
) -> VerifyPreanalysis:
    if ARGS().memory_encoding != "plain":
        return DEFAULT_VERIFY_PREANALYSIS
    from .memory_bus_alignment import analyze_memory_bus_partial_alignment_first

    alignment = analyze_memory_bus_partial_alignment_first(before, after)
    if alignment is not None:
        logger.info(
            "memory bus prealignment: n_before=%d n_after=%d aligned_pairs=%d",
            alignment.n_before,
            alignment.n_after,
            len(alignment.before_to_after),
        )
    return VerifyPreanalysis(memory_bus_alignment=alignment)


def apply_skip_trivial(before: dict[str, Any], after: dict[str, Any]) -> None:
    if not ARGS().skip_trivial or before != after:
        return
    logger.info("inputs are identical; stripping constraints and bus interactions")
    before["machine"]["constraints"] = []
    before["machine"]["bus_interactions"] = []
    after["machine"]["constraints"] = []
    after["machine"]["bus_interactions"] = []
