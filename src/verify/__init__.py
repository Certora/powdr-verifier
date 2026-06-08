"""Metadata merged into SMT-LIB scripts: pin equations and extra declarations."""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class SetInfo:
    """Skolem pin equations (``Equals`` / ``Iff``) and extra ``declare-fun`` symbols.

    Equations are turned into ``(set-info :skolem-derived-N ...)`` in
    :func:`~verifier.src.smt_backends.pysmt.convert_to_smt_script` with contiguous
    indices; merge fragments with ``+=`` without manual index offsets.
    """
    equations: list = field(default_factory=list)
    decls: list = field(default_factory=list)

    def __iadd__(self, other: SetInfo) -> SetInfo:
        self.equations.extend(other.equations)
        self.decls.extend(other.decls)
        return self
