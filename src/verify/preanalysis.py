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
        if not problems and not _interface_mults_const(before, after, after_assume_is_valid):
            if ARGS().interface_ignore_checks:
                # Same escape hatch as the explicit-interface path: with a clean
                # (identity-filled) kept alignment, still pick interface despite
                # non-const (is_valid/flag-gated) mults. The io_relation then
                # equates aligned args unconditionally (openvm_memory warns).
                logger.warning(
                    "interface-ignore-checks: auto selecting interface despite "
                    "non-const (is_valid/flag-gated) memory multiplicities"
                )
            else:
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


def _fold_is_valid_one(expr: Any) -> Any:
    """[is_valid=1 interface] Replace every ``is_valid`` column reference in a
    dumped expression with the constant 1. Remove with its caller once the
    interface encoder resolves is_valid-gated mults natively."""
    if isinstance(expr, str):
        return 1 if "is_valid" in expr else expr
    if isinstance(expr, list):
        return [_fold_is_valid_one(x) for x in expr]
    return expr


def _interface_mults_const(
    before: dict[str, Any], after: dict[str, Any], assume_is_valid: bool = False
) -> bool:
    """Mirror the interface encoding's precondition (openvm_memory.encode_all):
    every memory-bus multiplicity must const-evaluate to {0, +-1}. Conservative
    and syntactic — a multiplicity that references any column (e.g. the
    ``is_valid``- or flag-gated ``0 - is_valid``) is treated as non-const, so
    ``auto`` falls back to the always-sound plain encoding instead of letting
    the interface encoder abort with a hard error.

    When ``assume_is_valid`` (this analysis assumes is_valid==1, matching
    ``openvm_memory._active_mult``), is_valid selectors are folded to 1 first, so
    ``0 - is_valid`` counts as the const -1 and the interface encoding applies."""
    for dump in (before, after):
        machine = dump.get("machine", dump)
        mem_id = _memory_bus_id(dump)
        for bi in machine.get("bus_interactions", []):
            if bi.get("id") != mem_id:
                continue
            mult = bi.get("mult")
            if assume_is_valid:
                mult = _fold_is_valid_one(mult)
            if _expr_references_variable(mult):
                return False
    return True


def presolve_interface_eligible(
    before: dict[str, Any],
    after: dict[str, Any],
    kept_pairs: dict[int, int],
    removed_ids: set[int],
    n_before: int,
    n_after: int,
    *,
    after_assume_is_valid: bool = False,
) -> bool:
    """Decide, from ALIGN data + the syntactic mult-const check ONLY (no membus
    ``solve``), whether the interface encoding will be used — so the ~11s solve
    can be skipped when it will be.

    Mirrors the interface branch of :func:`analyze_memory_bus_alignment` /
    :func:`_alignment_problems`, minus the ``internal_pairs_for`` check: that one
    reads the solve-derived match sets, but the align-time
    ``_collect_internal_pairs`` (run inside ``run_membus_analysis``'s align loop,
    before the solve) already certifies the same internal-pair shape and *raises*
    on any malformation — so by the time we get here it is redundant.

    Conservative by construction: any doubt returns ``False`` (keep the solve).
    Plain always keeps the solve; a wrong ``True`` on a plain step would only
    leave the permutation unpinned (a perf regression), never be unsound."""
    if ARGS().memory_encoding not in ("interface", "auto"):
        return False
    if not kept_pairs:
        return False
    if not ARGS().interface_internal_pairs and removed_ids:
        return False
    if set(kept_pairs) & removed_ids:
        return False
    if set(kept_pairs) | removed_ids != set(range(n_before)):
        return False
    if sorted(kept_pairs.values()) != list(range(n_after)):
        return False
    if not _interface_mults_const(before, after, after_assume_is_valid):
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
