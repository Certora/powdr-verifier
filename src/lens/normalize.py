"""Signed-constant normalization for dump expressions.

powdr's two encodings represent a negative field element differently: the
``machine``/``AlgebraicExpression`` form uses a unary ``["-", c]``, while the
``constraints``/``GroupedExpression`` form uses the field residue (e.g.
``2013265920`` = p−1). To compare/display them uniformly we normalize every
constant toward its **signed** value modulo the BabyBear prime, so both render
as ``-1``.

This pass is representation-only: it rewrites constants and folds unary minus
over constants, but does NOT expand products or reassociate. (Full constraint
canonicalization — needed because ``loop_iteration`` also distributes — is a
separate, heavier step.)
"""
from __future__ import annotations

from typing import Any

from .metrics import FIELD_PRIME as BABYBEAR_PRIME

_HALF = BABYBEAR_PRIME // 2


def to_signed(v: int) -> int:
    """Map a field element to its signed representative in (−p/2, p/2].

    ``2013265920 → -1``, ``1 → 1``, ``p → 0``.
    """
    v %= BABYBEAR_PRIME
    return v - BABYBEAR_PRIME if v > _HALF else v


def normalize_constants(node: Any) -> Any:
    """Return ``node`` with every integer constant in signed form.

    Unary ``["-", e]`` is folded to a signed int when ``e`` is constant;
    over a non-constant it is kept as ``["-", e']`` (with ``e'`` normalized).
    """
    if isinstance(node, bool):
        return node
    if isinstance(node, int):
        return to_signed(node)
    if isinstance(node, str):
        return node
    if isinstance(node, list):
        if node and node[0] == "-" and len(node) == 2:  # unary minus
            inner = normalize_constants(node[1])
            return -inner if isinstance(inner, int) else ["-", inner]
        return [normalize_constants(x) for x in node]
    return node
