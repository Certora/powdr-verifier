"""Column-naming conventions — the one place name-based recognition lives.

Everything here is an instance of :data:`facts.Assumption.NAMING`: the openvm
/ powdr naming scheme identifies the timestamp domain and the activation
selector. These recognitions are *not* certifiable from the dump — a rename
would silently change what the extractor sees — so they are quarantined in
this module and declared as an assumption on every fact built from them.

Everything else in membus recognizes structure (constraint shapes, bus rows),
never names.
"""
from __future__ import annotations

import re

# ``<family>__0_<access>@<colid>`` — the low byte column of a register value.
# Used ONLY to render a readable label for an already-identified base column.
_FAM_RE = re.compile(r"(.+?)__0_(\d+)@\d+$")


def is_fs(col: str) -> bool:
    """A send timestamp column (the instruction clock ``from_state``)."""
    return "from_state__timestamp_" in col


def is_prev(col: str) -> bool:
    """A recv timestamp column (a ``prev_timestamp`` free witness)."""
    return "prev_timestamp" in col


def is_ts(col: str) -> bool:
    return is_fs(col) or is_prev(col)


def is_valid_col(col: str) -> bool:
    """The openvm autoprecompile activation selector ``is_valid`` (global —
    distinct from the per-instruction ``is_valid_<K>`` of early passes)."""
    return col.split("@", 1)[0] == "is_valid"


def fam_access(col: str) -> str:
    """Readable label for a base low-byte column (``rs1_data__0_0@3`` → ``rs1_0``)."""
    m = _FAM_RE.fullmatch(col)
    if not m:
        return col
    fam = m.group(1)
    fam = fam[:-5] if fam.endswith("_data") else fam   # rs1_data -> rs1
    return f"{fam}_{m.group(2)}"
