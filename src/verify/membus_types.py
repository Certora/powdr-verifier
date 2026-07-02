"""Memory-bus alignment types (no subprocess / bus_interactions imports)."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path


@dataclass(frozen=True)
class MembusParsedKey:
    kind: str
    const_value: int | None = None
    base: str | None = None
    offset: int | None = None


def parse_membus_key(key: str | None) -> MembusParsedKey | None:
    if not key:
        return None
    if key.startswith("const "):
        try:
            return MembusParsedKey("const", const_value=int(key[6:].strip()))
        except ValueError:
            return None
    if "+" in key and not key.startswith("unresolved"):
        base, off_s = key.rsplit("+", 1)
        if not base:
            return None
        try:
            return MembusParsedKey("base_offset", base=base, offset=int(off_s))
        except ValueError:
            return None
    return None


@dataclass
class AlignRowInfo:
    kind: str | None = None
    key: MembusParsedKey | None = None
    alias_class: int | None = None
    local_role: str | None = None
    local_partners: list[int] = field(default_factory=list)
    status: str | None = None
    after_id: int | None = None


@dataclass
class MembusAlignment:
    before_path: Path
    after_path: Path
    before_to_after: dict[int, int]
    before_rows: dict[int, AlignRowInfo]
    after_rows: dict[int, AlignRowInfo]

    @property
    def n_before(self) -> int:
        return len(self.before_rows)

    @property
    def n_after(self) -> int:
        return len(self.after_rows)
