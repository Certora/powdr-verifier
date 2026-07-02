from __future__ import annotations

import logging
from pathlib import Path
from typing import Any

from ..utils.args import ARGS
from .membus_align import run_membus_alignment
from .membus_types import MembusAlignment

logger = logging.getLogger(__name__)


def analyze_memory_bus_alignment(
    before: dict[str, Any], after: dict[str, Any]
) -> MembusAlignment | None:
    if ARGS().memory_encoding != "plain":
        return None

    alignment = run_membus_alignment(
        before,
        after,
        Path(ARGS().input_before),
        Path(ARGS().input_after),
    )
    logger.info(
        "memory bus prealignment: n_before=%d n_after=%d aligned_pairs=%d",
        alignment.n_before,
        alignment.n_after,
        len(alignment.before_to_after),
    )
    return alignment


def apply_skip_trivial(before: dict[str, Any], after: dict[str, Any]) -> None:
    if not ARGS().skip_trivial or before != after:
        return
    logger.info("inputs are identical; stripping constraints and bus interactions")
    before["machine"]["constraints"] = []
    before["machine"]["bus_interactions"] = []
    after["machine"]["constraints"] = []
    after["machine"]["bus_interactions"] = []
