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
        # 1:1 kept alignment AND the interface v1 precondition holds (every
        # memory multiplicity is const-evaluable to {0, +-1}); else fall back
        # to the always-sound plain encoding. Resolve the global once so every
        # downstream reader (encode / io-relation / pins) sees a concrete mode.
        problems = _alignment_problems(analysis)
        if not problems and not _interface_mults_const(before, after):
            problems = ["memory multiplicities are not const-evaluable (is_valid/flag-gated); interface v1 aborts"]
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


def _memory_bus_id(dump: dict[str, Any]) -> int:
    """Numeric id of the memory bus, from the dump's ``bus_map`` (default 1)."""
    bus_ids = (dump.get("bus_map") or {}).get("bus_ids") or {}
    for name, val in bus_ids.items():
        if "mem" in str(name).lower():
            if isinstance(val, int):
                return val
            if isinstance(val, dict) and isinstance(val.get("id"), int):
                return val["id"]
    return 1


def _expr_references_variable(expr: Any) -> bool:
    """True if a dumped algebraic expression references any (witness) column.

    Dumped expressions are ints, variable-name strings, or ``[lhs, op, rhs]``
    lists with ``op`` in ``{+,-,*}``. A bare string in operand position is a
    column reference."""
    if isinstance(expr, str):
        return expr not in ("+", "-", "*")
    if isinstance(expr, list):
        return any(_expr_references_variable(x) for x in expr)
    return False


def _interface_mults_const(before: dict[str, Any], after: dict[str, Any]) -> bool:
    """Mirror the interface encoding's precondition (openvm_memory.encode_all):
    every memory-bus multiplicity must const-evaluate to {0, +-1}. Conservative
    and syntactic — a multiplicity that references any column (e.g. the
    ``is_valid``- or flag-gated ``0 - is_valid``) is treated as non-const, so
    ``auto`` falls back to the always-sound plain encoding instead of letting
    the interface encoder abort with a hard error."""
    for dump in (before, after):
        machine = dump.get("machine", dump)
        mem_id = _memory_bus_id(dump)
        for bi in machine.get("bus_interactions", []):
            if bi.get("id") != mem_id:
                continue
            if _expr_references_variable(bi.get("mult")):
                return False
    return True


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
