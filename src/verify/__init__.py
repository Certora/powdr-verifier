"""Metadata merged into SMT-LIB scripts: pin equations and extra declarations."""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum

from pysmt.fnode import FNode


class SkolemPinKind(StrEnum):
    DERIVED = "derived"
    SUBSTITUTION = "substitution"
    MEMORY_BUS = "memory_bus"


SKOLEM_SETINFO_COLON_PREFIX = ":skolem-"


def skolem_setinfo_keyword_prefix(kind: SkolemPinKind) -> str:
    """``set-info`` keyword body without leading colon, e.g. ``skolem-derived-``."""
    return f"skolem-{kind.value.replace('_', '-')}-"


@dataclass(frozen=True)
class SkolemPin:
    node: FNode
    pin_type: SkolemPinKind


@dataclass
class SetInfos:
    """Skolem pins (``Equals`` / ``Iff`` / ``declare-fun`` targets) for SMT-LIB.

    Each entry carries its own :attr:`SkolemPin.pin_type`. Equations are turned
    into ``(set-info :skolem-<kind>-N ...)`` (per :func:`skolem_setinfo_keyword_prefix`)
    in :func:`~verifier.src.smt_backends.pysmt.convert_to_smt_script` with a single
    running index across all pins; merge fragments with ``+=`` without manual index offsets.
    """
    equations: list[SkolemPin] = field(default_factory=list)
    decls: list[SkolemPin] = field(default_factory=list)

    def __iadd__(self, other: SetInfos) -> SetInfos:
        self.equations.extend(other.equations)
        self.decls.extend(other.decls)
        return self
