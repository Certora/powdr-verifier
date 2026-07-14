from __future__ import annotations

import logging
from pathlib import Path
from typing import Any

from ..utils.args import ARGS
from .membus_analysis import MembusAnalysis, run_membus_analysis

logger = logging.getLogger(__name__)


def analyze_memory_bus_alignment(
    before: dict[str, Any],
    after: dict[str, Any],
    *,
    after_assume_is_valid: bool = False,
) -> MembusAnalysis | None:
    if ARGS().memory_encoding not in ("plain", "interface", "auto"):
        return None

    analysis = run_membus_analysis(
        before,
        after,
        Path(ARGS().input_before),
        Path(ARGS().input_after),
        after_assume_is_valid=after_assume_is_valid,
    )
    logger.warning(
        "membus alignment: %s to %s (after_assume_is_valid=%s)",
        analysis.before_path,
        analysis.after_path,
        after_assume_is_valid,
    )
    if ARGS().memory_encoding == "interface":
        # Explicit request: a non-perfect alignment is a hard error.
        _require_perfect_alignment(analysis)
    elif ARGS().memory_encoding == "auto":
        # Pick the interface encoding when the analysis certifies a perfect
        # 1:1 kept alignment, else fall back to the always-sound plain
        # encoding. Resolve the global once so every downstream reader (encode
        # / io-relation / pins) sees a concrete mode; a later call (e.g. the
        # is_valid-inactive analysis) re-checks its own alignment under the
        # resolved mode.
        problems = _alignment_problems(analysis)
        resolved = "plain" if problems else "interface"
        logger.warning(
            "auto memory-encoding -> %s (%s)",
            resolved,
            "; ".join(problems) if problems else "perfect 1:1 kept alignment",
        )
        ARGS().memory_encoding = resolved
    return analysis


def _alignment_problems(analysis: MembusAnalysis) -> list[str]:
    """Reasons the alignment is not a perfect 1:1 kept map, or ``[]`` if it is.

    The interface encoding assumes recv equalities across aligned pairs, so a
    wrong or partial pairing is a soundness risk (vacuous premises = false
    PASS). Only a total 1:1 map sourced from genuine ``membus align`` "kept"
    rows qualifies — never the heuristic fallback or identity fill."""
    n = analysis.n_before
    kept = analysis.kept_pairs
    problems: list[str] = []
    if not analysis.align_ok:
        problems.append("membus align did not run (heuristic fallback)")
    if analysis.n_after != n:
        problems.append(
            f"interaction counts differ (before={n}, after={analysis.n_after})"
        )
    if set(kept) != set(range(n)):
        problems.append(
            f"kept pairs are not total on the before side ({len(kept)}/{n} kept)"
        )
    elif sorted(kept.values()) != list(range(analysis.n_after)):
        problems.append("kept pairs are not a bijection onto the after side")
    return problems


def _require_perfect_alignment(analysis: MembusAnalysis) -> None:
    """Raise unless ``analysis`` is a perfect 1:1 kept alignment (see
    :func:`_alignment_problems`). Used by the explicit ``interface`` mode."""
    problems = _alignment_problems(analysis)
    if problems:
        raise RuntimeError(
            "interface memory encoding requires a perfect 1:1 kept alignment: "
            + "; ".join(problems)
        )


def apply_skip_trivial(before: dict[str, Any], after: dict[str, Any]) -> None:
    if not ARGS().skip_trivial or before != after:
        return
    logger.info("inputs are identical; stripping constraints and bus interactions")
    before["machine"]["constraints"] = []
    before["machine"]["bus_interactions"] = []
    after["machine"]["constraints"] = []
    after["machine"]["bus_interactions"] = []
