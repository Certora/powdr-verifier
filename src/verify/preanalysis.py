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
        _require_interface_alignment(analysis)
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

    The interface encoding assumes recv equalities across aligned pairs (and,
    with ``--interface-internal-pairs``, grants recv==send equalities for the
    forced interior pairs among the removed interactions), so a wrong or
    partial pairing is a soundness risk (vacuous premises = false PASS). Accept
    only a map sourced from genuine ``membus align`` rows — never the heuristic
    fallback or identity fill — in which the before side partitions into kept
    interactions and removed ones (each removed interaction inert or one leg of
    a forced interior pair), and the kept pairs are a bijection onto the after
    side."""
    n = analysis.n_before
    kept = analysis.kept_pairs
    removed = analysis.removed_for(analysis.before_path)
    problems: list[str] = []
    # No explicit "align ran?" check: on the heuristic fallback (any-or-all
    # address spaces missing) the unaligned interactions land in neither `kept`
    # nor `removed`, so the coverage check below rejects them anyway.
    if not ARGS().interface_internal_pairs and removed:
        problems.append(
            f"{len(removed)} removed interaction(s) present but "
            "--no-interface-internal-pairs is set"
        )
    if set(kept) & removed:
        problems.append("kept pairs and removed interactions overlap")
    if set(kept) | removed != set(range(n)):
        problems.append(
            f"before interactions not fully accounted for "
            f"({len(kept)} kept, {len(removed)} removed, of {n})"
        )
    if sorted(kept.values()) != list(range(analysis.n_after)):
        problems.append("kept pairs are not a bijection onto the after side")
    # The non-inert removed interactions must pair up as forced mutual
    # match-singletons — the recovered recv==send equalities depend on it.
    try:
        analysis.internal_pairs_for(analysis.before_path)
    except RuntimeError as exc:
        problems.append(str(exc))
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


def _require_interface_alignment(analysis: MembusAnalysis) -> None:
    """Raise unless ``analysis`` is a kept alignment covering all interactions
    (modulo forced internal pairs; see :func:`_alignment_problems`). Used by the
    explicit ``interface`` mode."""
    problems = _alignment_problems(analysis)
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
