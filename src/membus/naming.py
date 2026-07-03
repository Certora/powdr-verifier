"""Human-facing column labels — display only, never load-bearing.

The fact layer identifies the timestamp domain and the activation selector
**positionally/structurally** (membus argument slots, constraint shapes — see
`rules.Analysis`); no extraction rule depends on a column's name. This module
only renders names for humans: readable base labels and the instruction index
shown by `info`.
"""
from __future__ import annotations

import re

# ``<family>__0_<access>@<colid>`` — the low byte column of a register value.
_FAM_RE = re.compile(r"(.+?)__0_(\d+)@\d+$")


def fam_access(col: str) -> str:
    """Readable label for a base low-byte column (``rs1_data__0_0@3`` → ``rs1_0``)."""
    m = _FAM_RE.fullmatch(col)
    if not m:
        return col
    fam = m.group(1)
    fam = fam[:-5] if fam.endswith("_data") else fam   # rs1_data -> rs1
    return f"{fam}_{m.group(2)}"


def access_index(col: str) -> int | None:
    """Instruction index K from a ``..._<K>@<n>`` column name (display only)."""
    m = re.search(r"_(\d+)@\d+$", col)
    return int(m.group(1)) if m else None
