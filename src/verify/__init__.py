"""Metadata merged into SMT-LIB scripts: ``set-info`` pins and extra declarations."""
from dataclasses import dataclass, field


@dataclass
class SetInfo:
    """Combined set-info commands and extra declarations for an SMT script."""
    cmds: list = field(default_factory=list)
    decls: list = field(default_factory=list)

    def __iadd__(self, other: "SetInfo") -> "SetInfo":
        self.cmds.extend(other.cmds)
        self.decls.extend(other.decls)
        return self


def combine_setinfo(*parts: SetInfo) -> SetInfo:
    result = SetInfo()
    for p in parts:
        result += p
    return result
