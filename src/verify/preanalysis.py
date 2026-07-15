from __future__ import annotations

import logging
from pathlib import Path
from typing import Any

from ..utils.args import ARGS
from .membus_analysis import MembusAnalysis, run_membus_analysis

logger = logging.getLogger(__name__)


def analyze_memory_bus_alignment(
    before: dict[str, Any], after: dict[str, Any]
) -> MembusAnalysis | None:
    if ARGS().memory_encoding not in ("plain", "interface"):
        return None

    analysis = run_membus_analysis(
        before,
        after,
        Path(ARGS().input_before),
        Path(ARGS().input_after),
    )
    logger.warning(
        "membus alignment: %s to %s",
        analysis.before_path,
        analysis.after_path,
    )
    if ARGS().memory_encoding == "interface":
        _require_interface_alignment(analysis)
    return analysis


def _require_interface_alignment(analysis: MembusAnalysis) -> None:
    """The interface encoding assumes recv equalities across aligned pairs (and,
    with ``--interface-internal-pairs``, grants recv==send equalities for the
    forced interior pairs among the removed interactions), so a wrong or
    partial pairing is a soundness risk (vacuous premises = false PASS).
    Accept only a map sourced from genuine ``membus align`` rows — never the
    heuristic fallback or identity fill — in which every before interaction is
    kept, one leg of a forced internal pair, or inert, and the kept pairs are
    a bijection onto the after side."""
    n = analysis.n_before
    kept = analysis.kept_pairs
    pairs = analysis.internal_pairs_before
    inert = analysis.inert_removed_before
    problems = []
    if not analysis.align_ok:
        problems.append("membus align did not run (heuristic fallback)")
    if not ARGS().interface_internal_pairs and (pairs or inert):
        problems.append(
            f"{len(pairs)} internal pair(s) / {len(inert)} inert removed present "
            "but --no-interface-internal-pairs is set"
        )
    legs = {p.recv for p in pairs} | {p.send for p in pairs}
    if len(legs) != 2 * len(pairs):
        problems.append("internal pair legs are not pairwise distinct")
    if legs & set(kept) or legs & inert or set(kept) & inert:
        problems.append("kept pairs, internal pair legs, and inert rows overlap")
    if set(kept) | legs | inert != set(range(n)):
        problems.append(
            f"before interactions not fully accounted for ({len(kept)} kept, "
            f"{len(legs)} internal-pair legs, {len(inert)} inert, of {n})"
        )
    if sorted(kept.values()) != list(range(analysis.n_after)):
        problems.append("kept pairs are not a bijection onto the after side")
    if problems:
        raise RuntimeError(
            "interface memory encoding requires a kept alignment covering all "
            "interactions (modulo forced internal pairs): " + "; ".join(problems)
        )


def apply_skip_trivial(before: dict[str, Any], after: dict[str, Any]) -> None:
    if not ARGS().skip_trivial or before != after:
        return
    logger.info("inputs are identical; stripping constraints and bus interactions")
    before["machine"]["constraints"] = []
    before["machine"]["bus_interactions"] = []
    after["machine"]["constraints"] = []
    after["machine"]["bus_interactions"] = []
